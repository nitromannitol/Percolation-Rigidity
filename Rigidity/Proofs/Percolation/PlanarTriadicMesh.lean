import Rigidity.Percolation.TriadicWellConnectedUnion
import Rigidity.Proofs.Section5.LoopFromCrossings
import Rigidity.Proofs.Percolation.PlanarBoxGeometry

/-!
# Strip meshes in planar integer cubes

An integer cube `R = c + [0, S)²` of `ℤ²` carries a mesh of width `w` when every horizontal strip
`[c₀, c₀ + S - 1] × [r, r + w]` and every vertical strip `[r, r + w] × [c₁, c₁ + S - 1]` inside `R`
has an open crossing in its long direction, inside the strip. By the crossing lemma all these
crossings lie in one open component of `R`, the component of the start of the bottom horizontal
crossing (the hub), and every open path inside `R` whose endpoints differ by at least `w` in some
coordinate joins that component inside `R`. Consequently the cube is crossable, open paths of
large coordinate diameter coalesce, and, with a mesh in an ambient cube, they are anchored to its
crossing components.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The horizontal strip `[c₀, c₀ + S - 1] × [r, r + w]` of an integer cube. -/
def IntegerCube.hStrip (R : IntegerCube 2) (r : ℤ) (w : ℕ) : Set (Vertex 2) :=
  {v | (R.corner 0 ≤ v 0 ∧ v 0 ≤ R.corner 0 + ((R.size - 1 : ℕ) : ℤ)) ∧ r ≤ v 1 ∧ v 1 ≤ r + w}

/-- The vertical strip `[r, r + w] × [c₁, c₁ + S - 1]` of an integer cube. -/
def IntegerCube.vStrip (R : IntegerCube 2) (r : ℤ) (w : ℕ) : Set (Vertex 2) :=
  {v | (r ≤ v 0 ∧ v 0 ≤ r + w) ∧ R.corner 1 ≤ v 1 ∧ v 1 ≤ R.corner 1 + ((R.size - 1 : ℕ) : ℤ)}

/-- Every strip of width `w` of the cube has an open crossing in its long direction. -/
def PlanarMesh (ω : Configuration 2) (R : IntegerCube 2) (w : ℕ) : Prop :=
  (∀ r : ℤ, R.corner 1 ≤ r → r + w + 1 ≤ R.corner 1 + R.size →
    ∃ a b, ReachIn ω (R.hStrip r w) a b ∧ a 0 = R.corner 0 ∧
      b 0 = R.corner 0 + ((R.size - 1 : ℕ) : ℤ)) ∧
  (∀ r : ℤ, R.corner 0 ≤ r → r + w + 1 ≤ R.corner 0 + R.size →
    ∃ a b, ReachIn ω (R.vStrip r w) a b ∧ a 1 = R.corner 1 ∧
      b 1 = R.corner 1 + ((R.size - 1 : ℕ) : ℤ))

theorem IntegerCube.size_sub_one_cast {R : IntegerCube 2} (h : 1 ≤ R.size) :
    ((R.size - 1 : ℕ) : ℤ) = R.size - 1 := by
  push_cast [Nat.cast_sub h]
  ring

/-- Coordinates of a vertex of an integer cube. -/
theorem IntegerCube.coord_of_mem {R : IntegerCube 2} {v : Vertex 2}
    (hv : v ∈ (↑R.vertices : Set (Vertex 2))) (i : Fin 2) :
    R.corner i ≤ v i ∧ v i + 1 ≤ R.corner i + R.size := by
  have h := ((IntegerCube.mem_vertices R v).1 hv) i
  omega

theorem IntegerCube.hStrip_subset {R : IntegerCube 2} {r : ℤ} {w : ℕ}
    (hr : R.corner 1 ≤ r) (hrw : r + w + 1 ≤ R.corner 1 + R.size) :
    R.hStrip r w ⊆ ↑R.vertices := by
  intro v hv
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hv
  have hs : 1 ≤ R.size := by omega
  rw [IntegerCube.size_sub_one_cast hs] at h2
  rw [Finset.mem_coe, IntegerCube.mem_vertices]
  intro i
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> omega

theorem IntegerCube.vStrip_subset {R : IntegerCube 2} {r : ℤ} {w : ℕ}
    (hr : R.corner 0 ≤ r) (hrw : r + w + 1 ≤ R.corner 0 + R.size) :
    R.vStrip r w ⊆ ↑R.vertices := by
  intro v hv
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hv
  have hs : 1 ≤ R.size := by omega
  rw [IntegerCube.size_sub_one_cast hs] at h4
  rw [Finset.mem_coe, IntegerCube.mem_vertices]
  intro i
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> omega

/-- Membership in a lower face of an integer cube. -/
theorem IntegerCube.mem_lowerFace_coe {R : IntegerCube 2} {i : Fin 2} {v : Vertex 2} :
    v ∈ (↑(R.lowerFace i) : Set (Vertex 2)) ↔ v ∈ (↑R.vertices : Set (Vertex 2)) ∧
      v i = R.corner i := by
  simp only [IntegerCube.lowerFace, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe]

/-- Membership in an upper face of an integer cube. -/
theorem IntegerCube.mem_upperFace_coe {R : IntegerCube 2} {i : Fin 2} {v : Vertex 2} :
    v ∈ (↑(R.upperFace i) : Set (Vertex 2)) ↔ v ∈ (↑R.vertices : Set (Vertex 2)) ∧
      v i + 1 = R.corner i + R.size := by
  simp only [IntegerCube.upperFace, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe]

/-- **The hub of a mesh.** In a cube with a mesh of width `w < S`, the start of the bottom
horizontal crossing reaches, inside the cube, both faces in each direction, and the start of every
open path inside the cube whose endpoints differ by at least `w` in some coordinate. -/
theorem PlanarMesh.exists_hub {R : IntegerCube 2} {w : ℕ} (hmesh : PlanarMesh ω R w)
    (hw : w + 1 ≤ R.size) :
    ∃ hub ∈ (↑R.vertices : Set (Vertex 2)),
      (∀ (c d : Vertex 2) (k : Fin 2), ReachIn ω ↑R.vertices c d → c k + w ≤ d k →
        ReachIn ω ↑R.vertices hub c) ∧
      ∀ i : Fin 2,
        (∃ y ∈ (↑R.vertices : Set (Vertex 2)), y ∈ (↑(R.lowerFace i) : Set (Vertex 2)) ∧
          ReachIn ω ↑R.vertices hub y) ∧
        (∃ y ∈ (↑R.vertices : Set (Vertex 2)), y ∈ (↑(R.upperFace i) : Set (Vertex 2)) ∧
          ReachIn ω ↑R.vertices hub y) := by
  have hs : 1 ≤ R.size := by omega
  have hcast := IntegerCube.size_sub_one_cast hs
  set B : Set (Vertex 2) := ↑R.vertices with hBdef
  have hBrow : ∀ v ∈ B, R.corner 1 ≤ v 1 ∧ v 1 ≤ R.corner 1 + ((R.size - 1 : ℕ) : ℤ) := by
    intro v hv
    have := IntegerCube.coord_of_mem hv 1
    rw [hcast]
    omega
  have hBcol : ∀ v ∈ B, R.corner 0 ≤ v 0 ∧ v 0 ≤ R.corner 0 + ((R.size - 1 : ℕ) : ℤ) := by
    intro v hv
    have := IntegerCube.coord_of_mem hv 0
    rw [hcast]
    omega
  obtain ⟨h0s, h0e, hH0, hh0s, hh0e⟩ := hmesh.1 (R.corner 1) le_rfl (by omega)
  obtain ⟨v0s, v0e, hV0, hv0s, hv0e⟩ := hmesh.2 (R.corner 0) le_rfl (by omega)
  have hHsub := IntegerCube.hStrip_subset (R := R) (r := R.corner 1) (w := w) le_rfl (by omega)
  have hVsub := IntegerCube.vStrip_subset (R := R) (r := R.corner 0) (w := w) le_rfl (by omega)
  -- the hub reaches every vertical crossing
  have hubV : ∀ (r : ℤ) (a b : Vertex 2), R.corner 0 ≤ r → r + w + 1 ≤ R.corner 0 + R.size →
      ReachIn ω (R.vStrip r w) a b → a 1 = R.corner 1 →
      b 1 = R.corner 1 + ((R.size - 1 : ℕ) : ℤ) → ReachIn ω B h0s a := by
    intro r a b hr hrw hab ha hb
    obtain ⟨z, hz1, hz2⟩ := exists_reachIn_of_crossing hH0 hab
      (xa := r) (xb := r + w) (ya := R.corner 1) (yb := R.corner 1 + w)
      (fun v hv => hv.2) (fun v hv => hv.1) (by rw [hh0s]; exact hr)
      (by rw [hh0e, hcast]; omega) (by rw [ha]) (by rw [hb, hcast]; omega)
    exact (hz1.mono hHsub).trans (hz2.mono (IntegerCube.vStrip_subset hr hrw)).symm
  -- the hub reaches every horizontal crossing
  have hubH : ∀ (r : ℤ) (a b : Vertex 2), R.corner 1 ≤ r → r + w + 1 ≤ R.corner 1 + R.size →
      ReachIn ω (R.hStrip r w) a b → a 0 = R.corner 0 →
      b 0 = R.corner 0 + ((R.size - 1 : ℕ) : ℤ) → ReachIn ω B h0s a := by
    intro r a b hr hrw hab ha hb
    have h1 := hubV (R.corner 0) v0s v0e le_rfl (by omega) hV0 hv0s hv0e
    obtain ⟨z, hz1, hz2⟩ := exists_reachIn_of_crossing hab hV0
      (xa := R.corner 0) (xb := R.corner 0 + w) (ya := r) (yb := r + w)
      (fun v hv => hv.2) (fun v hv => hv.1) (by rw [ha])
      (by rw [hb, hcast]; omega) (by rw [hv0s]; exact hr) (by rw [hv0e, hcast]; omega)
    exact h1.trans ((hz2.mono hVsub).trans (hz1.mono (IntegerCube.hStrip_subset hr hrw)).symm)
  have hh0sB : h0s ∈ B := hHsub hH0.start_mem
  refine ⟨h0s, hh0sB, ?_, ?_⟩
  · intro c d k hcd hk
    have hcB := hcd.start_mem
    have hdB := hcd.end_mem
    fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue] at hk
      have hc0 := hBcol c hcB
      have hd0 := IntegerCube.coord_of_mem hdB 0
      obtain ⟨a, b, hab, ha, hb⟩ := hmesh.2 (c 0) hc0.1 (by omega)
      obtain ⟨z, hz1, hz2⟩ := exists_reachIn_of_crossing hcd hab
        (xa := c 0) (xb := c 0 + w) (ya := R.corner 1) (yb := R.corner 1 + ((R.size - 1 : ℕ) : ℤ))
        hBrow (fun v hv => hv.1) le_rfl hk (by rw [ha]) (by rw [hb])
      exact (hubV (c 0) a b hc0.1 (by omega) hab ha hb).trans
        ((hz2.mono (IntegerCube.vStrip_subset hc0.1 (by omega))).trans hz1.symm)
    · simp only [Fin.mk_one, Fin.isValue] at hk
      have hc1 := hBrow c hcB
      have hd1 := IntegerCube.coord_of_mem hdB 1
      obtain ⟨a, b, hab, ha, hb⟩ := hmesh.1 (c 1) hc1.1 (by omega)
      obtain ⟨z, hz1, hz2⟩ := exists_reachIn_of_crossing hab hcd
        (xa := R.corner 0) (xb := R.corner 0 + ((R.size - 1 : ℕ) : ℤ)) (ya := c 1) (yb := c 1 + w)
        (fun v hv => hv.2) hBcol (by rw [ha]) (by rw [hb]) le_rfl hk
      exact (hubH (c 1) a b hc1.1 (by omega) hab ha hb).trans
        ((hz1.mono (IntegerCube.hStrip_subset hc1.1 (by omega))).trans hz2.symm)
  · intro i
    have hv0sB : v0s ∈ B := hVsub hV0.start_mem
    have hv0eB : v0e ∈ B := hVsub hV0.end_mem
    have hh0eB : h0e ∈ B := hHsub hH0.end_mem
    have hub_v0s := hubV (R.corner 0) v0s v0e le_rfl (by omega) hV0 hv0s hv0e
    fin_cases i
    · refine ⟨⟨h0s, hh0sB, IntegerCube.mem_lowerFace_coe.2 ⟨hh0sB, hh0s⟩,
        reachIn_of_reachable_openIn hh0sB (SimpleGraph.Reachable.refl _)⟩,
        ⟨h0e, hh0eB, IntegerCube.mem_upperFace_coe.2 ⟨hh0eB, by
          change h0e 0 + 1 = R.corner 0 + R.size
          rw [hh0e, hcast]; ring⟩, hH0.mono hHsub⟩⟩
    · exact ⟨⟨v0s, hv0sB, IntegerCube.mem_lowerFace_coe.2 ⟨hv0sB, hv0s⟩, hub_v0s⟩,
        ⟨v0e, hv0eB, IntegerCube.mem_upperFace_coe.2 ⟨hv0eB, by
          change v0e 1 + 1 = R.corner 1 + R.size
          rw [hv0e, hcast]; ring⟩, hub_v0s.trans (hV0.mono hVsub)⟩⟩

/-- The vertices of a chain of open edges inside a region, started in the region, lie in the region
and are joined to its start inside the region. -/
theorem chain_reachable {d : ℕ} {ω : Configuration d} {B : Set (Vertex d)} {n : ℕ}
    {γ : Fin (n + 1) → Vertex d} (h0 : γ 0 ∈ B)
    (hadj : ∀ i : Fin n, (openIn ω B).Adj (γ i.castSucc) (γ i.succ)) :
    ∀ i : Fin (n + 1), γ i ∈ B ∧ (openIn ω B).Reachable (γ 0) (γ i) := by
  intro i
  induction i using Fin.induction with
  | zero => exact ⟨h0, SimpleGraph.Reachable.refl _⟩
  | succ i ih =>
    have h := hadj i
    exact ⟨h.2.2, ih.2.trans h.reachable⟩

/-- The vertices of a walk inside a region, as a chain of open edges inside the region. -/
theorem chain_of_walk {d : ℕ} {ω : Configuration d} {B : Set (Vertex d)} {u v : Vertex d}
    (W : (openGraph ω).Walk u v) (hW : ∀ z ∈ W.support, z ∈ B) :
    ∀ i : Fin W.length, (openIn ω B).Adj (W.getVert (i.castSucc : Fin (W.length + 1)))
      (W.getVert (i.succ : Fin (W.length + 1))) := by
  intro i
  refine ⟨?_, hW _ (W.getVert_mem_support _), hW _ (W.getVert_mem_support _)⟩
  have h := W.adj_getVert_succ (i := (i : ℕ)) i.isLt
  simpa only [Fin.val_castSucc, Fin.val_succ] using h

/-- In a cube with a mesh of width `w`, `10 w ≤ side`, all selected paths of a triadic cube of the
given side start in one open component of the cube. -/
theorem PlanarMesh.largePathsCoalesce {R : IntegerCube 2} {w : ℕ} (hmesh : PlanarMesh ω R w)
    (hw : w + 1 ≤ R.size) (Q : TriadicCube 2) (hside : 10 * (w : ℤ) ≤ Q.side) :
    LargePathsCoalesce ω ↑R.vertices Q.largePath := by
  obtain ⟨hub, -, hdisp, -⟩ := hmesh.exists_hub hw
  have hsel : ∀ n γ, IsSelectedOpenPath ω ↑R.vertices Q.largePath n γ →
      ReachIn ω ↑R.vertices hub (γ 0) := by
    intro n γ ⟨⟨i, j, k, hij⟩, h0, hadj⟩
    have hci := chain_reachable h0 hadj
    have hi := hci i
    have hj := hci j
    have hreach : ReachIn ω ↑R.vertices (γ i) (γ j) :=
      reachIn_of_reachable_openIn hi.1 (hi.2.symm.trans hj.2)
    have hi0 : ReachIn ω ↑R.vertices (γ i) (γ 0) :=
      reachIn_of_reachable_openIn hi.1 hi.2.symm
    have hj0 : ReachIn ω ↑R.vertices (γ j) (γ 0) :=
      reachIn_of_reachable_openIn hj.1 hj.2.symm
    rcases le_total (γ i k) (γ j k) with hle | hle
    · have hk : γ i k + w ≤ γ j k := by
        rw [abs_of_nonpos (by linarith)] at hij
        linarith
      exact (hdisp _ _ k hreach hk).trans hi0
    · have hk : γ j k + w ≤ γ i k := by
        rw [abs_of_nonneg (by linarith)] at hij
        linarith
      exact (hdisp _ _ k hreach.symm hk).trans hj0
  intro n γ hγ m η hη
  exact reachIn_reachable_openIn ((hsel n γ hγ).symm.trans (hsel m η hη))

/-- A cube with a mesh of width `w < S` is crossable. -/
theorem PlanarMesh.crossableRegion {R : IntegerCube 2} {w : ℕ} (hmesh : PlanarMesh ω R w)
    (hw : w + 1 ≤ R.size) :
    CrossableRegion ω ↑R.vertices (fun i => ↑(R.lowerFace i)) (fun i => ↑(R.upperFace i)) := by
  obtain ⟨hub, -, -, hfaces⟩ := hmesh.exists_hub hw
  intro i
  obtain ⟨⟨y, hy, hyl, hhy⟩, ⟨y', hy', hyu, hhy'⟩⟩ := hfaces i
  exact ⟨y, hy, y', hy', hyl, hyu, reachIn_reachable_openIn (hhy.symm.trans hhy')⟩

/-- A cube with a mesh of width `w < S` has a crossing component. -/
theorem PlanarMesh.hasCrossingComponent {R : IntegerCube 2} {w : ℕ} (hmesh : PlanarMesh ω R w)
    (hw : w + 1 ≤ R.size) :
    HasCrossingComponent ω ↑R.vertices (fun i => ↑(R.lowerFace i))
      (fun i => ↑(R.upperFace i)) := by
  obtain ⟨hub, hhub, -, hfaces⟩ := hmesh.exists_hub hw
  refine ⟨hub, hhub, fun i => ?_⟩
  obtain ⟨⟨y, hy, hyl, hhy⟩, ⟨y', hy', hyu, hhy'⟩⟩ := hfaces i
  exact ⟨⟨y, hy, hyl, reachIn_reachable_openIn hhy⟩, ⟨y', hy', hyu, reachIn_reachable_openIn hhy'⟩⟩

/-- The integer and centered descriptions of a triadic cube give the same vertex set. -/
theorem TriadicCube.coe_toIntegerCube_vertices (Q : TriadicCube 2) :
    (↑Q.toIntegerCube.vertices : Set (Vertex 2)) = Q.vertices :=
  Set.ext fun x => Q.mem_toIntegerCube_vertices x

/-- **Anchoring in planar cubes.** Let a triadic cube `Q` and an integer cube `R` carry meshes of
width `w`, with a column strip and a row strip of width `w` lying in both. If `Q` has a crossing
root and `R` contains a selected path of `Q`, then some selected path of `R` starts in the
component of the root inside `Q`. -/
theorem PlanarMesh.hasAnchoredLargePath {Q : TriadicCube 2} {R : IntegerCube 2} {w : ℕ}
    (hQ : PlanarMesh ω Q.toIntegerCube w) (hR : PlanarMesh ω R w)
    (hwQ : w + 1 ≤ Q.toIntegerCube.size) {L0 L1 : ℤ}
    (hL0R : R.corner 0 ≤ L0) (hL0R' : L0 + w + 1 ≤ R.corner 0 + R.size)
    (hL0Q : Q.toIntegerCube.corner 0 ≤ L0)
    (hL0Q' : L0 + w + 1 ≤ Q.toIntegerCube.corner 0 + Q.toIntegerCube.size)
    (hL1R : R.corner 1 ≤ L1) (hL1R' : L1 + w + 1 ≤ R.corner 1 + R.size)
    (hL1Q : Q.toIntegerCube.corner 1 ≤ L1)
    (hL1Q' : L1 + w + 1 ≤ Q.toIntegerCube.corner 1 + Q.toIntegerCube.size)
    {root : Vertex 2}
    (hroot : IsCrossingRoot ω Q.vertices (fun i => ↑(Q.toIntegerCube.lowerFace i))
      (fun i => ↑(Q.toIntegerCube.upperFace i)) root)
    (hsel : HasSelectedOpenPath ω ↑R.vertices Q.largePath) :
    HasAnchoredLargePath ω ↑R.vertices Q.vertices root Q.largePath := by
  set Qc := Q.toIntegerCube with hQc
  have hQs : 1 ≤ Qc.size := by omega
  have hRs : 1 ≤ R.size := by omega
  have hQcast := IntegerCube.size_sub_one_cast hQs
  have hRcast := IntegerCube.size_sub_one_cast hRs
  have hQset : (↑Qc.vertices : Set (Vertex 2)) = Q.vertices := Q.coe_toIntegerCube_vertices
  have hQcol : ∀ v ∈ Q.vertices,
      Qc.corner 0 ≤ v 0 ∧ v 0 ≤ Qc.corner 0 + ((Qc.size - 1 : ℕ) : ℤ) := by
    intro v hv
    rw [← hQset] at hv
    have := IntegerCube.coord_of_mem hv 0
    rw [hQcast]
    omega
  -- the root component crosses `Q` vertically
  obtain ⟨-, hroot⟩ := hroot
  obtain ⟨⟨yb, hybQ, hybl, hryb⟩, ⟨yt, hytQ, hytu, hryt⟩⟩ := hroot 1
  have hyb1 : yb 1 = Qc.corner 1 := (IntegerCube.mem_lowerFace_coe.1 hybl).2
  have hyt1 : yt 1 + 1 = Qc.corner 1 + Qc.size := (IntegerCube.mem_upperFace_coe.1 hytu).2
  have hPv : ReachIn ω Q.vertices yb yt := reachIn_of_reachable_openIn hybQ (hryb.symm.trans hryt)
  -- crossings of the meshes
  obtain ⟨hs, he, hH, hhs, hhe⟩ := hQ.1 (Qc.corner 1) le_rfl (by omega)
  obtain ⟨vs, ve, hV, hvs, hve⟩ := hQ.2 L0 hL0Q hL0Q'
  obtain ⟨a, b, hRh, ha, hb⟩ := hR.1 L1 hL1R hL1R'
  have hHsub : Qc.hStrip (Qc.corner 1) w ⊆ Q.vertices :=
    hQset ▸ IntegerCube.hStrip_subset le_rfl (by omega)
  have hVsub : Qc.vStrip L0 w ⊆ Q.vertices := hQset ▸ IntegerCube.vStrip_subset hL0Q hL0Q'
  have hRsub : R.hStrip L1 w ⊆ ↑R.vertices := IntegerCube.hStrip_subset hL1R hL1R'
  obtain ⟨u1, hu1h, hu1v⟩ := exists_reachIn_of_crossing hH hPv
    (xa := Qc.corner 0) (xb := Qc.corner 0 + ((Qc.size - 1 : ℕ) : ℤ))
    (ya := Qc.corner 1) (yb := Qc.corner 1 + w) (fun v hv => hv.2) hQcol
    (by rw [hhs]) (by rw [hhe]) (by rw [hyb1]) (by omega)
  obtain ⟨u2, hu2h, hu2v⟩ := exists_reachIn_of_crossing hH hV
    (xa := L0) (xb := L0 + w) (ya := Qc.corner 1) (yb := Qc.corner 1 + w)
    (fun v hv => hv.2) (fun v hv => hv.1) (by rw [hhs]; exact hL0Q)
    (by rw [hhe, hQcast]; omega) (by rw [hvs]) (by rw [hve, hQcast]; omega)
  obtain ⟨z, hzR, hzV⟩ := exists_reachIn_of_crossing hRh hV
    (xa := L0) (xb := L0 + w) (ya := L1) (yb := L1 + w)
    (fun v hv => hv.2) (fun v hv => hv.1) (by rw [ha]; exact hL0R)
    (by rw [hb, hRcast]; omega) (by rw [hvs]; exact hL1Q) (by rw [hve, hQcast]; omega)
  have hrootz : (openIn ω Q.vertices).Reachable root z := by
    refine hryb.trans (reachIn_reachable_openIn ?_)
    exact hu1v.trans ((hu1h.mono hHsub).symm.trans ((hu2h.mono hHsub).trans
      ((hu2v.mono hVsub).symm.trans (hzV.mono hVsub))))
  -- the selected path through the row crossing of `R`
  obtain ⟨n', γ', ⟨i', j', k', h'⟩, h0', hadj'⟩ := hsel
  have hci := chain_reachable h0' hadj'
  have hspan : Q.side ≤ 10 * (((R.size - 1 : ℕ) : ℤ)) := by
    have hi := IntegerCube.coord_of_mem (hci i').1 k'
    have hj := IntegerCube.coord_of_mem (hci j').1 k'
    have habs : |γ' i' k' - γ' j' k'| ≤ ((R.size - 1 : ℕ) : ℤ) := by
      rw [abs_le, hRcast]
      constructor <;> omega
    linarith
  obtain ⟨W1, hW1⟩ := hzR.symm
  obtain ⟨W2, hW2⟩ := hRh
  let W := W1.append W2
  have hWsub : ∀ v ∈ W.support, v ∈ (↑R.vertices : Set (Vertex 2)) := by
    intro v hv
    rcases (SimpleGraph.Walk.mem_support_append_iff W1 W2).1 hv with hv | hv
    exacts [hRsub (hW1 v hv), hRsub (hW2 v hv)]
  have haW : a ∈ W.support := (SimpleGraph.Walk.mem_support_append_iff W1 W2).2
    (Or.inr W2.start_mem_support)
  obtain ⟨ia, hia, hia'⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 haW
  refine ⟨W.length, fun i => W.getVert i,
    ⟨⟨⟨ia, by omega⟩, Fin.last _, 0, ?_⟩, ?_, chain_of_walk W hWsub⟩, ?_⟩
  · simp only [Fin.val_last, SimpleGraph.Walk.getVert_length]
    rw [hia, ha, hb]
    rw [show R.corner 0 - (R.corner 0 + ((R.size - 1 : ℕ) : ℤ)) =
      -((R.size - 1 : ℕ) : ℤ) by ring, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
    exact hspan
  · simpa only [Fin.val_zero, SimpleGraph.Walk.getVert_zero] using hWsub z W.start_mem_support
  · simpa only [Fin.val_zero, SimpleGraph.Walk.getVert_zero] using hrootz

end Rigidity.Percolation
