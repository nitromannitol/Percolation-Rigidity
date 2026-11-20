import Rigidity.Proofs.Percolation.PlanarTriadicMesh
import Rigidity.Proofs.Percolation.KestenCrossing
import Rigidity.Proofs.Section5.PlanarCrossingEvents
import Rigidity.Percolation.TriadicLargeScaleDecay
import Rigidity.Percolation.TriadicWellConnectedDecay
import Rigidity.Percolation.TriadicThreeQuarterCube

/-!
# The triadic partition of good cubes in the plane

For supercritical planar bond percolation, a triadic cube `Q` of side `s = 3ⁿ` is well-connected
relative to its rounded three-quarter cube (`TriadicCube.wellConnectedIn`) outside an event of
probability at most `C exp(-c s)`. On the event that `Q` and all its test cubes carry strip meshes
of width `⌊s/100⌋`, `Q` has a crossing component, every test cube is crossable, its selected paths
coalesce and are anchored to the crossing components of `Q` (`PlanarTriadicMesh.lean`); Kesten's
rectangle crossing estimate bounds the failure of each mesh by `C s² exp(-c ⌊s/100⌋)`, and the
number of test cubes is polynomial in `s`. The partition estimates of the stopping construction
(Armstrong and Dario, Proposition 2.1) then hold in dimension two.
-/

open MeasureTheory Filter LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped ENNReal

namespace Rigidity.Percolation

/-- Failure of a strip mesh in an integer cube, from Kesten's rectangle crossing estimate. -/
theorem measure_not_planarMesh_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (R : IntegerCube 2) (w : ℕ),
      latticeBondLaw 2 p {ω | ¬ PlanarMesh ω R w} ≤
        ENNReal.ofReal (2 * (((R.size : ℝ) + 1) * (C * ((R.size : ℝ) + 1) *
          Real.exp (-(c * w))))) := by
  obtain ⟨C, c, hC, hc, hK⟩ := Rigidity.Percolation.kesten_rectangle_crossing p hpc
  refine ⟨C, c, hC, hc, fun R w => ?_⟩
  set μ := latticeBondLaw 2 p
  set f : ℝ := C * ((R.size : ℝ) + 1) * Real.exp (-(c * w)) with hf
  have hf0 : 0 ≤ f := by positivity
  have hterm : ∀ (x : Vertex 2) (i : Fin 2),
      μ {ω | ¬ HasOpenCrossing ω x (R.size - 1) w i} ≤ ENNReal.ofReal f := by
    intro x i
    refine (hK x (R.size - 1) w i).trans (ENNReal.ofReal_le_ofReal ?_)
    have hle : ((R.size - 1 : ℕ) : ℝ) + 1 ≤ (R.size : ℝ) + 1 := by
      have : ((R.size - 1 : ℕ) : ℝ) ≤ R.size := by exact_mod_cast Nat.sub_le _ _
      linarith
    have he : 0 ≤ Real.exp (-(c * w)) := (Real.exp_pos _).le
    rw [hf]
    gcongr
  set rows := Finset.Icc (R.corner 1) (R.corner 1 + R.size)
  set cols := Finset.Icc (R.corner 0) (R.corner 0 + R.size)
  have hsub : {ω | ¬ PlanarMesh ω R w} ⊆
      (⋃ r ∈ rows, {ω | ¬ HasOpenCrossing ω ![R.corner 0, r] (R.size - 1) w 0}) ∪
      (⋃ r ∈ cols, {ω | ¬ HasOpenCrossing ω ![r, R.corner 1] (R.size - 1) w 1}) := by
    intro ω hω
    by_contra hcon
    apply hω
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists,
      not_not] at hcon
    obtain ⟨h1, h2⟩ := hcon
    constructor
    · intro r hr hrw
      exact exists_reachIn_of_hasOpenCrossing_zero
        (h1 r (Finset.mem_Icc.2 ⟨hr, by omega⟩))
    · intro r hr hrw
      exact exists_reachIn_of_hasOpenCrossing_one
        (h2 r (Finset.mem_Icc.2 ⟨hr, by omega⟩))
  have hcard : ∀ a : ℤ, ((Finset.Icc a (a + R.size)).card : ℝ) = (R.size : ℝ) + 1 := by
    intro a
    rw [Int.card_Icc]
    have : (a + R.size + 1 - a).toNat = R.size + 1 := by omega
    rw [this]
    push_cast
    ring
  have hrows := measure_biUnion_le_card_mul μ rows
    (fun r => {ω | ¬ HasOpenCrossing ω ![R.corner 0, r] (R.size - 1) w 0}) (f := f)
    (fun r _ => hterm _ _)
  have hcols := measure_biUnion_le_card_mul μ cols
    (fun r => {ω | ¬ HasOpenCrossing ω ![r, R.corner 1] (R.size - 1) w 1}) (f := f)
    (fun r _ => hterm _ _)
  rw [hcard] at hrows hcols
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add hrows hcols).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- A test cube of a triadic cube of side at least `1000` shares with it a strip of width
`w ≤ side/100` in each coordinate. -/
theorem TriadicCube.exists_common_strip {Q : TriadicCube 2} {R : IntegerCube 2}
    {interior : Set (Vertex 2)} (hint : interior ⊆ Q.threeQuarterEnvelope)
    (hR : R ∈ Q.testCubes interior) {w : ℕ} (hw : 100 * w ≤ 3 ^ Q.scale)
    (hs : 1000 ≤ 3 ^ Q.scale) (i : Fin 2) :
    ∃ L : ℤ, R.corner i ≤ L ∧ L + w + 1 ≤ R.corner i + R.size ∧
      Q.toIntegerCube.corner i ≤ L ∧
      L + w + 1 ≤ Q.toIntegerCube.corner i + Q.toIntegerCube.size := by
  obtain ⟨hR1, hR2, x, hxR, hxI⟩ := hR
  have henv := hint hxI i
  have hx := (IntegerCube.mem_vertices R x).1 hxR i
  have hside : Q.side = ((3 ^ Q.scale : ℕ) : ℤ) := by
    simp only [TriadicCube.side, Nat.cast_pow, Nat.cast_ofNat]
  have hodd : Q.side % 2 = 1 := by
    have ho : Odd Q.side := by
      dsimp only [TriadicCube.side]
      exact (show Odd (3 : ℤ) from ⟨1, by norm_num⟩).pow
    exact Int.odd_iff.mp ho
  have hw' : 100 * (w : ℤ) ≤ Q.side := by rw [hside]; exact_mod_cast hw
  have hs' : 1000 ≤ Q.side := by rw [hside]; exact_mod_cast hs
  have hcorner : Q.toIntegerCube.corner i = Q.side * Q.index i - Q.side / 2 := rfl
  have hsize : (Q.toIntegerCube.size : ℤ) = Q.side := by
    rw [hside]; rfl
  have hcenter : Q.center i = Q.side * Q.index i := rfl
  rw [hcenter] at henv
  have ha1 := le_abs_self (2 * (x i - Q.side * Q.index i))
  have ha2 := neg_abs_le (2 * (x i - Q.side * Q.index i))
  rw [hcorner, hsize]
  generalize Q.side * Q.index i = c at *
  by_cases hcase : (w : ℤ) ≤ x i - R.corner i
  · exact ⟨x i - w, by omega, by omega, by omega, by omega⟩
  · exact ⟨x i, by omega, by omega, by omega, by omega⟩

/-- On meshes of width `⌊side/100⌋` in a triadic cube of side at least `1000` and in a test cube,
the local test of well-connectedness succeeds. -/
theorem TriadicCube.badCoalescenceTest_subset_planarMesh {Q : TriadicCube 2} {R : IntegerCube 2}
    {interior : Set (Vertex 2)} (hint : interior ⊆ Q.threeQuarterEnvelope)
    (hR : R ∈ Q.testCubes interior) (hs : 1000 ≤ 3 ^ Q.scale) :
    Q.badCoalescenceTest R ⊆ {ω | ¬ PlanarMesh ω Q.toIntegerCube (3 ^ Q.scale / 100)} ∪
      {ω | ¬ PlanarMesh ω R (3 ^ Q.scale / 100)} := by
  set w := 3 ^ Q.scale / 100 with hwdef
  have hw : 100 * w ≤ 3 ^ Q.scale := Nat.mul_div_le _ _
  have hside : Q.side = ((3 ^ Q.scale : ℕ) : ℤ) := by
    simp only [TriadicCube.side, Nat.cast_pow, Nat.cast_ofNat]
  obtain ⟨hR1, hR2, -⟩ := id hR
  have hRw : w + 1 ≤ R.size := by
    have : (3 ^ Q.scale : ℕ) ≤ 10 * R.size := by
      have h := hR1
      rw [hside] at h
      exact_mod_cast h
    omega
  have hQw : w + 1 ≤ Q.toIntegerCube.size := by
    change w + 1 ≤ 3 ^ Q.scale
    omega
  have h10 : 10 * (w : ℤ) ≤ Q.side := by
    rw [hside]
    exact_mod_cast (show 10 * w ≤ 3 ^ Q.scale by omega)
  intro ω hω
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
  obtain ⟨hQm, hRm⟩ := hcon
  obtain ⟨L0, h0R, h0R', h0Q, h0Q'⟩ := Q.exists_common_strip hint hR hw hs 0
  obtain ⟨L1, h1R, h1R', h1Q, h1Q'⟩ := Q.exists_common_strip hint hR hw hs 1
  rcases hω with h | h | ⟨root, hroot, hfail⟩
  · exact h (hRm.crossableRegion hRw)
  · exact h (hRm.largePathsCoalesce hRw Q h10)
  · exact hfail fun hsel => PlanarMesh.hasAnchoredLargePath hQm hRm hQw h0R h0R' h0Q h0Q'
      h1R h1R' h1Q h1Q' hroot hsel

/-- On a mesh of a triadic cube of side at least `1000`, the cube has a crossing component. -/
theorem TriadicCube.not_hasCrossingComponent_subset_planarMesh (Q : TriadicCube 2)
    (hs : 1000 ≤ 3 ^ Q.scale) :
    {ω | ¬ HasCrossingComponent ω Q.vertices (fun i => ↑(Q.toIntegerCube.lowerFace i))
        (fun i => ↑(Q.toIntegerCube.upperFace i))} ⊆
      {ω | ¬ PlanarMesh ω Q.toIntegerCube (3 ^ Q.scale / 100)} := by
  intro ω hω hmesh
  apply hω
  rw [← Q.coe_toIntegerCube_vertices]
  exact hmesh.hasCrossingComponent (by change 3 ^ Q.scale / 100 + 1 ≤ 3 ^ Q.scale; omega)

/-- A polynomial factor `(s + 1)²` costs half of an exponential rate. -/
theorem sq_add_one_mul_exp_neg_le {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    (s + 1) ^ 2 * Real.exp (-(a * s)) ≤ (max 1 (4 / a)) ^ 2 * Real.exp (-(a / 2 * s)) := by
  set M := max 1 (4 / a)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM4 : 4 / a ≤ M := le_max_right _ _
  have hlin : s + 1 ≤ M * (a * s / 4 + 1) := by
    have h4 : s ≤ M * (a * s / 4) := by
      have : 4 / a * (a * s / 4) = s := by field_simp
      calc s = 4 / a * (a * s / 4) := this.symm
        _ ≤ M * (a * s / 4) := by gcongr
    nlinarith
  have hexp : (a * s / 4 + 1) ^ 2 ≤ Real.exp (a / 2 * s) := by
    have h := Real.add_one_le_exp (a * s / 4)
    have h0 : 0 ≤ a * s / 4 + 1 := by positivity
    calc (a * s / 4 + 1) ^ 2 ≤ Real.exp (a * s / 4) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = Real.exp (a / 2 * s) := by rw [← Real.exp_nat_mul]; ring_nf
  have hsq : (s + 1) ^ 2 ≤ M ^ 2 * Real.exp (a / 2 * s) := by
    calc (s + 1) ^ 2 ≤ (M * (a * s / 4 + 1)) ^ 2 := pow_le_pow_left₀ (by linarith) hlin 2
      _ = M ^ 2 * (a * s / 4 + 1) ^ 2 := by ring
      _ ≤ M ^ 2 * Real.exp (a / 2 * s) := by gcongr
  calc (s + 1) ^ 2 * Real.exp (-(a * s)) ≤ M ^ 2 * Real.exp (a / 2 * s) * Real.exp (-(a * s)) :=
        mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ = M ^ 2 * Real.exp (-(a / 2 * s)) := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf

/-- **Well-connectedness of planar triadic cubes.** For `p > p_c(2)`, triadic cubes of side at
least `3⁷` are well-connected relative to their rounded three-quarter cubes outside an event of
probability at most `C exp(-c · 3ⁿ)`. -/
theorem planar_wellConnectedIn_large_scale {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ Q : TriadicCube 2, 7 ≤ Q.scale →
      latticeBondLaw 2 p {ω | ¬ Q.wellConnectedIn Q.threeQuarterCube.vertices ω} ≤
        ENNReal.ofReal (C * Real.exp (-c * (3 : ℝ) ^ Q.scale)) := by
  obtain ⟨C, c, hC, hc, hmesh⟩ := measure_not_planarMesh_le hpc
  set a : ℝ := c / 100 with hadef
  have ha : 0 < a := by positivity
  set M : ℝ := max 1 (4 / a)
  set C1 : ℝ := 4 * C * Real.exp c * M ^ 2 with hC1def
  set c1 : ℝ := a / 2 with hc1def
  have hC1 : 0 ≤ C1 := by positivity
  have hc1 : 0 < c1 := by positivity
  set A : ℝ := 2 * 7 ^ 2 * ((2 + 1).factorial : ℝ) / (c1 / 2) ^ (2 + 1)
  refine ⟨C1 * (1 + A), c1 / 2, by positivity, by positivity, fun Q hQ => ?_⟩
  have hs : 1000 ≤ 3 ^ Q.scale := by
    calc 1000 ≤ 3 ^ 7 := by norm_num
      _ ≤ 3 ^ Q.scale := Nat.pow_le_pow_right (by norm_num) hQ
  set w := 3 ^ Q.scale / 100 with hwdef
  set s : ℝ := (3 : ℝ) ^ Q.scale with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hsize : ((Q.toIntegerCube.size : ℕ) : ℝ) = s := by
    change ((3 ^ Q.scale : ℕ) : ℝ) = _
    push_cast
    rfl
  have hwlow : s / 100 - 1 ≤ (w : ℝ) := by
    have h : 3 ^ Q.scale < 100 * (w + 1) := by
      have := Nat.lt_mul_div_succ (3 ^ Q.scale) (show 0 < 100 by norm_num)
      omega
    have h' : ((3 ^ Q.scale : ℕ) : ℝ) < 100 * ((w : ℝ) + 1) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hexpw : Real.exp (-(c * w)) ≤ Real.exp c * Real.exp (-(a * s)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [hadef]
    nlinarith
  have hB : 4 * C * (s + 1) ^ 2 * Real.exp (-(c * w)) ≤ C1 * Real.exp (-c1 * s) := by
    have hpoly := sq_add_one_mul_exp_neg_le ha hs0
    calc 4 * C * (s + 1) ^ 2 * Real.exp (-(c * w))
        ≤ 4 * C * (s + 1) ^ 2 * (Real.exp c * Real.exp (-(a * s))) := by gcongr
      _ = 4 * C * Real.exp c * ((s + 1) ^ 2 * Real.exp (-(a * s))) := by ring
      _ ≤ 4 * C * Real.exp c * (M ^ 2 * Real.exp (-(a / 2 * s))) := by gcongr
      _ = C1 * Real.exp (-c1 * s) := by rw [hC1def, hc1def]; ring_nf
  have hmeshQ : latticeBondLaw 2 p {ω | ¬ PlanarMesh ω Q.toIntegerCube w} ≤
      ENNReal.ofReal (C1 * Real.exp (-c1 * s)) := by
    refine (hmesh _ _).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hsize]
    have he : 0 ≤ Real.exp (-(c * w)) := (Real.exp_pos _).le
    have hpos : 0 ≤ 2 * C * (s + 1) ^ 2 * Real.exp (-(c * w)) := by positivity
    calc 2 * ((s + 1) * (C * (s + 1) * Real.exp (-(c * w))))
        = 2 * C * (s + 1) ^ 2 * Real.exp (-(c * w)) := by ring
      _ ≤ 4 * C * (s + 1) ^ 2 * Real.exp (-(c * w)) := by linarith
      _ ≤ C1 * Real.exp (-c1 * s) := hB
  have hint : (↑Q.threeQuarterCube.vertices : Set (Vertex 2)) ⊆ Q.threeQuarterEnvelope :=
    Q.threeQuarterCube_subset_envelope
  refine (Q.measure_not_wellConnectedIn_le_exp _ (hint.trans Q.threeQuarterEnvelope_subset)
    (latticeBondLaw 2 p) C1 c1 hC1 hc1 ?_ ?_).trans (le_of_eq ?_)
  · exact (measure_mono (Q.not_hasCrossingComponent_subset_planarMesh hs)).trans hmeshQ
  · intro R hR
    have hRs : (R.size : ℝ) ≤ s := by
      have h := hR.2.1
      have h' : (2 * R.size : ℕ) ≤ 3 ^ Q.scale := by
        have : (2 * (R.size : ℤ)) ≤ ((3 ^ Q.scale : ℕ) : ℤ) := by
          simpa [TriadicCube.side] using h
        exact_mod_cast this
      have h'' : ((2 * R.size : ℕ) : ℝ) ≤ ((3 ^ Q.scale : ℕ) : ℝ) := by exact_mod_cast h'
      push_cast at h''
      linarith
    have hmeshR : latticeBondLaw 2 p {ω | ¬ PlanarMesh ω R w} ≤
        ENNReal.ofReal (2 * C * (s + 1) ^ 2 * Real.exp (-(c * w))) := by
      refine (hmesh _ _).trans (ENNReal.ofReal_le_ofReal ?_)
      have he : 0 ≤ Real.exp (-(c * w)) := (Real.exp_pos _).le
      have h1 : (R.size : ℝ) + 1 ≤ s + 1 := by linarith
      have h0 : (0 : ℝ) ≤ R.size + 1 := by positivity
      calc 2 * (((R.size : ℝ) + 1) * (C * ((R.size : ℝ) + 1) * Real.exp (-(c * w))))
          = 2 * C * ((R.size : ℝ) + 1) ^ 2 * Real.exp (-(c * w)) := by ring
        _ ≤ 2 * C * (s + 1) ^ 2 * Real.exp (-(c * w)) := by gcongr
    have hmeshQ' : latticeBondLaw 2 p {ω | ¬ PlanarMesh ω Q.toIntegerCube w} ≤
        ENNReal.ofReal (2 * C * (s + 1) ^ 2 * Real.exp (-(c * w))) := by
      refine (hmesh _ _).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      rw [hsize]
      ring
    refine (measure_mono (Q.badCoalescenceTest_subset_planarMesh hint hR hs)).trans
      ((measure_union_le _ _).trans ((add_le_add hmeshQ' hmeshR).trans ?_))
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) hB)
    ring
  · congr 2

/-- **The planar partition of good cubes** (Armstrong and Dario, Proposition 2.1, in dimension
two). For `p > p_c(2)`, almost surely the maximal stopping cubes of the good triadic cubes
partition `ℤ²`, their sizes have uniform exponential moments, and the partition is approximately
local. -/
theorem planar_triadic_partition_estimates {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    let G : Configuration 2 → Set (TriadicCube 2) := fun ω =>
      TriadicCube.goodOfWellConnected (TriadicCube.wellConnectedFamily
        (fun Q => Q.threeQuarterCube.vertices) ω)
    (∀ᵐ ω ∂(latticeBondLaw 2 p), ∀ x : Vertex 2,
      ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (G ω)) ∧
    (∃ θ : ℝ, 0 < θ ∧ ∀ x : Vertex 2,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (G ω) x / θ)) (latticeBondLaw 2 p) ∧
      (∫ ω, Real.exp (TriadicCube.stoppingSize (G ω) x / θ) ∂(latticeBondLaw 2 p)) ≤ 2) ∧
    (∃ K k : ℝ, 0 < K ∧ 0 < k ∧ ∀ (A : TriadicCube 2) (n : ℕ),
      (latticeBondLaw 2 p) {ω | ∃ x ∈ A.boundaryInterior n, ∃ Q R : TriadicCube 2,
        x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
          R.IsMaximalStopping (TriadicCube.localGoodCentered (G ω) A.vertices) ∧ Q ≠ R} ≤
        ENNReal.ofReal (K * (3 : ℝ) ^ ((A.scale : ℝ) - n) *
          Real.exp (-k * (3 : ℝ) ^ n))) := by
  obtain ⟨C, c, hC, hc, hlarge⟩ := planar_wellConnectedIn_large_scale hpc
  exact TriadicCube.partition_estimates_of_large_scale (by norm_num) (latticeBondLaw 2 p)
    (fun Q => Q.threeQuarterCube.vertices) 7 C c hC hc hlarge

end Rigidity.Percolation
