import Rigidity.Percolation.FaceSeedPad

/-!
# Connecting a seed to an outward pad

Above criticality, a centered seed connects with arbitrarily high probability
to a fully open translate of itself in a controlled outward pad.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External Filter
open scoped Topology

/-- The central seed reaches a face vertex joined by an open bond to an
open translate of the seed contained in the outward pad. -/
def padSeedSuccess {d : ℕ} (M n : ℕ) (i : Fin d) : Set (Configuration d) :=
  {ω | ∃ y ∈ centeredBondCubeFinset M,
    ∃ x ∈ centeredCubeOrthantFace n i (fun _ => true),
    (openIn ω (centeredBondCube n)).Reachable y x ∧
    ∃ c : Vertex d, let S := (fun z : Vertex d => z + c) '' centeredBondCube M
      S ⊆ orthantFaceSeedPad n (2 * M + 1) i ∧ ω ∈ fullyOpenRegion S ∧
      (fun j => if j = i then x j + 1 else x j) ∈ S ∧
      (openGraph ω).Adj x (fun j => if j = i then x j + 1 else x j)}

/-- The event of reaching an open translated seed in the pad is measurable. -/
theorem measurableSet_padSeedSuccess {d : ℕ} (M n : ℕ) (i : Fin d) :
    MeasurableSet (padSeedSuccess M n i) := by
  let S : Vertex d → Set (Vertex d) := fun c => (fun z : Vertex d => z + c) '' centeredBondCube M
  let step : Vertex d → Vertex d := fun x j => if j = i then x j + 1 else x j
  have heq : padSeedSuccess M n i = ⋃ y ∈ centeredBondCubeFinset M,
      ⋃ x ∈ centeredCubeOrthantFace n i (fun _ => true),
      {ω | (openIn ω (centeredBondCube n)).Reachable y x} ∩ ⋃ c,
        {ω | S c ⊆ orthantFaceSeedPad n (2 * M + 1) i} ∩
        fullyOpenRegion (S c) ∩ {ω | step x ∈ S c} ∩
        {ω | (openGraph ω).Adj x (step x)} := by
    ext ω
    simp only [padSeedSuccess, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, S, step]
    constructor
    · rintro ⟨y, hy, x, hx, hpath, c, hpad, hopen, hstep, hedge⟩
      exact ⟨y, hy, x, hx, hpath, c, ⟨⟨⟨hpad, hopen⟩, hstep⟩, hedge⟩⟩
    · rintro ⟨y, hy, x, hx, hpath, c, ⟨⟨⟨hpad, hopen⟩, hstep⟩, hedge⟩⟩
      exact ⟨y, hy, x, hx, hpath, c, hpad, hopen, hstep, hedge⟩
  rw [heq]
  refine MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _ =>
      (measurableSet_openIn_reachable _ y x).inter (MeasurableSet.iUnion fun c => ?_)
  exact (((MeasurableSet.const (S c ⊆ orthantFaceSeedPad n (2 * M + 1) i)).inter
    (bondSigma_le (localBonds (S c)) _ (measurableSet_fullyOpenRegion_localBond (S c)))).inter
      (MeasurableSet.const (step x ∈ S c))).inter (measurableSet_openGraph_adj x (step x))

/-- For an aligned face, a successful outward trial realizes a seed in the
corresponding pad joined to the contact by an open bond. -/
theorem singleFieldSeedFaceSuccess_subset_padSeedSuccess {d : ℕ} (M n : ℕ)
    (i : Fin d) (hdiv : ((2 * M + 1 : ℕ) : ℤ) ∣ (n : ℤ) + 1) :
    singleFieldSeedFaceSuccess (centeredBondCube n) (centeredBondCubeFinset M)
      (centeredCubeOrthantFace n i (fun _ => true)) (2 * M + 1) i n ⊆
        padSeedSuccess M n i := by
  intro ω hω
  obtain ⟨y, hy, x, hx, hpath, htrial⟩ := hω
  let k := 2 * M + 1
  have hk : 0 < k := by dsimp [k]; omega
  have hxi : x i = (n : ℤ) := by
    have h := ((mem_centeredCubeOrthantFace n i (fun _ => true) x).mp hx).2.1
    simpa only [↓reduceIte] using h
  let c : Vertex d := fun j =>
    (if j = i then (n : ℤ) + 1 else (k : ℤ) * seedGridIndex k x j) + (M : ℤ)
  have hcell : faceSeedCell k i n (seedGridIndex k x) =
      (fun z : Vertex d => z + c) '' centeredBondCube M :=
    faceSeedCell_eq_centeredCube_translate M i n x
  let z : Vertex d := fun j => if j = i then x j + 1 else x j
  have hz : z ∈ faceSeedCell k i n (seedGridIndex k x) :=
    face_contact_step_mem_seed hk i n x hxi
  have hadj : (nearestNeighborGraph d).Adj x z := face_contact_step_adj i x
  have he : bondOfAdjacent hadj ∈ localBonds (faceSeedTrial k i n x) := by
    intro w hw
    change w ∈ s(x, z) at hw
    rcases Sym2.mem_iff.mp hw with hw | hw
    · rw [hw]
      exact Set.mem_insert x _
    · rw [hw]
      exact Set.mem_insert_of_mem _ hz
  have hopen : (openGraph ω).Adj x z :=
    (openGraph_adj_iff ω x z).mpr ⟨hadj, htrial _ he⟩
  refine ⟨y, hy, x, hx, hpath, c, ?_, ?_, ?_, hopen⟩
  · rw [← hcell]
    exact faceSeedCell_subset_orthantFaceSeedPad hk n i x hx hdiv
  · rw [← hcell]
    exact fullyOpenRegion_faceSeed_of_trial i n x htrial
  · rw [← hcell]
    exact hz

/-- For every positive integer `k`, arbitrarily large offsets make the
corresponding cube width divisible by `k`. -/
theorem exists_large_aligned_offset (M N k : ℕ) (hk : 0 < k) :
    ∃ n : ℕ, N ≤ n ∧ M < n ∧ k ∣ M + n + 1 := by
  let L := N + 3 * M + 2
  let n := k * L - (M + 1)
  have hL : L ≤ k * L := Nat.le_mul_of_pos_left L hk
  change N + 3 * M + 2 ≤ k * L at hL
  have hsub : M + 1 ≤ k * L := by omega
  have heq : M + n + 1 = k * L := by dsimp [n]; omega
  refine ⟨n, ?_, ?_, ⟨L, heq⟩⟩ <;> omega

/-- Above the critical probability, a positive centered seed connects with
arbitrarily high probability to an open translate of itself in the outward
face pad of a larger centered cube. -/
theorem exists_padSeedSuccess_of_supercritical {d : ℕ} [NeZero d]
    (p : unitInterval) (hp : criticalProbability d < (p : ℝ))
    (i : Fin d) (η : ℝ) (hη : 0 < η) :
    ∃ M n : ℕ, 0 < M ∧ 2 * M < n ∧
      1 - η < (latticeBondLaw d p).real (padSeedSuccess M n i) := by
  obtain ⟨M, hMpos, hM⟩ :=
    exists_seed_eventually_singleFieldFaceSuccess_of_supercritical p hp i η hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp hM
  obtain ⟨n, hn, hMn, hdiv⟩ := exists_large_aligned_offset M N (2 * M + 1) (by omega)
  have hdiv' : ((2 * M + 1 : ℕ) : ℤ) ∣ ((M + n : ℕ) : ℤ) + 1 := by
    exact_mod_cast hdiv
  refine ⟨M, M + n, hMpos, by omega, ?_⟩
  apply (hN n hn).trans_le
  exact measureReal_mono (singleFieldSeedFaceSuccess_subset_padSeedSuccess M (M + n) i hdiv')
    (measure_ne_top _ _)

end Rigidity.Percolation
