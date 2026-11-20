import Rigidity.Percolation.Blocks.LinkEvents
import Rigidity.Percolation.Blocks.GridPeierls

/-!
# Blocks in a slab box

A slab box has two long sides of length `S` in the directions `i ≠ j` and thin sides of length
`w = 12m + 1` in the other directions. Blocks are centred on a square grid of mesh `10m` in the
plane of `i, j`, at distance `11m` from the faces of the box and in the middle of the thin sides.
The block at `s` is good when the uniqueness zone at its centre holds and the four links to the
neighbouring blocks hold. The good event of a block depends only on the bonds of a box of radius
`11m` (`6m` in the thin directions) around its centre, inside the slab box; blocks at grid
distance at least three use disjoint boxes.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

variable {d : ℕ}

/-- The slab box with long sides `S` in the directions `i, j` and thin sides `w`. -/
def slabBox (lo : Vertex d) (i j : Fin d) (S w : ℕ) : Set (Vertex d) :=
  {x | ∀ l, lo l ≤ x l ∧ x l < lo l + if l = i ∨ l = j then (S : ℤ) else w}

/-- The centre of the block `s`. -/
def blockCentre (lo : Vertex d) (i j : Fin d) (m : ℕ) (s : ℤ × ℤ) : Vertex d :=
  fun l => lo l + if l = i then 11 * (m : ℤ) + 10 * m * s.1 else
    if l = j then 11 * (m : ℤ) + 10 * m * s.2 else 6 * m

/-- The box of the bonds used by the block `s`. -/
def blockRegion (lo : Vertex d) (i j : Fin d) (m : ℕ) (s : ℤ × ℤ) : Set (Vertex d) :=
  {v | ∀ l, |v l - blockCentre lo i j m s l| ≤ if l = i ∨ l = j then 11 * (m : ℤ) else 6 * m}

/-- The good event of the block `s`. -/
def blockGood (lo : Vertex d) (i j : Fin d) (m u n : ℕ) (s : ℤ × ℤ) : Set (Configuration d) :=
  {ω | UniqueZone ω (blockCentre lo i j m s) u n} ∩
    linkEvent (blockCentre lo i j m s) i m u ∩ linkEvent (blockCentre lo i j m s) j m u ∩
    linkEvent (blockCentre lo i j m (s - (1, 0))) i m u ∩
    linkEvent (blockCentre lo i j m (s - (0, 1))) j m u

theorem blockCentre_apply_i {lo : Vertex d} {i j : Fin d} {m : ℕ} {s : ℤ × ℤ} :
    blockCentre lo i j m s i = lo i + 11 * m + 10 * m * s.1 := by
  simp [blockCentre, add_assoc]

theorem blockCentre_apply_j {lo : Vertex d} {i j : Fin d} (hij : i ≠ j) {m : ℕ} {s : ℤ × ℤ} :
    blockCentre lo i j m s j = lo j + 11 * m + 10 * m * s.2 := by
  simp [blockCentre, Ne.symm hij, add_assoc]

theorem blockCentre_apply_other {lo : Vertex d} {i j l : Fin d} (hi : l ≠ i) (hj : l ≠ j)
    {m : ℕ} {s : ℤ × ℤ} : blockCentre lo i j m s l = lo l + 6 * m := by
  simp [blockCentre, hi, hj]

/-- The next block in the direction `i`. -/
theorem blockCentre_add_i {lo : Vertex d} {i j : Fin d} (hij : i ≠ j) (m : ℕ) (s : ℤ × ℤ) :
    blockCentre lo i j m s + offsetVec i ((10 * m : ℕ) : ℤ) = blockCentre lo i j m (s + (1, 0)) := by
  funext l
  simp only [Pi.add_apply, offsetVec_apply, blockCentre, Prod.fst_add, Prod.snd_add]
  by_cases hl : l = i
  · subst hl
    simp only [↓reduceIte]
    push_cast
    ring
  · by_cases hlj : l = j
    · subst hlj
      simp [hl]
    · simp [hl, hlj]

/-- The next block in the direction `j`. -/
theorem blockCentre_add_j {lo : Vertex d} {i j : Fin d} (hij : i ≠ j) (m : ℕ) (s : ℤ × ℤ) :
    blockCentre lo i j m s + offsetVec j ((10 * m : ℕ) : ℤ) = blockCentre lo i j m (s + (0, 1)) := by
  funext l
  simp only [Pi.add_apply, offsetVec_apply, blockCentre, Prod.fst_add, Prod.snd_add]
  by_cases hl : l = i
  · subst hl
    simp [hij]
  · by_cases hlj : l = j
    · subst hlj
      simp only [hl, ↓reduceIte]
      push_cast
      ring
    · simp [hl, hlj]

/-- A cube whose centre is close enough to a block centre lies in the block region. -/
theorem cubeAt_subset_blockRegion {lo : Vertex d} {i j : Fin d} {m : ℕ} {s : ℤ × ℤ}
    {c : Vertex d} {r : ℕ}
    (h : ∀ l, -((if l = i ∨ l = j then 11 * (m : ℤ) else 6 * m) - r) ≤
        c l - blockCentre lo i j m s l ∧
      c l - blockCentre lo i j m s l ≤ (if l = i ∨ l = j then 11 * (m : ℤ) else 6 * m) - r) :
    cubeAt c r ⊆ blockRegion lo i j m s := by
  intro v hv l
  have h1 := abs_le.1 (hv l)
  rw [abs_le]
  constructor <;> linarith [(h l).1, (h l).2]

/-- The previous block in the direction `i`. -/
theorem blockCentre_sub_i {lo : Vertex d} {i j : Fin d} (hij : i ≠ j) (m : ℕ) (s : ℤ × ℤ) :
    blockCentre lo i j m (s - (1, 0)) = blockCentre lo i j m s - offsetVec i ((10 * m : ℕ) : ℤ) := by
  rw [eq_sub_iff_add_eq, blockCentre_add_i hij]
  simp

/-- The previous block in the direction `j`. -/
theorem blockCentre_sub_j {lo : Vertex d} {i j : Fin d} (hij : i ≠ j) (m : ℕ) (s : ℤ × ℤ) :
    blockCentre lo i j m (s - (0, 1)) = blockCentre lo i j m s - offsetVec j ((10 * m : ℕ) : ℤ) := by
  rw [eq_sub_iff_add_eq, blockCentre_add_j hij]
  simp

/-- The bonds of the uniqueness zone and of the four links of a block lie in its region. -/
theorem blockGood_cubes_subset {lo : Vertex d} {i j : Fin d} (hij : i ≠ j) {m n : ℕ}
    (hn : n ≤ 6 * m) (s : ℤ × ℤ) :
    cubeAt (blockCentre lo i j m s) n ⊆ blockRegion lo i j m s ∧
    cubeAt (blockCentre lo i j m s + offsetVec i ((5 * m : ℕ) : ℤ)) (6 * m) ⊆
      blockRegion lo i j m s ∧
    cubeAt (blockCentre lo i j m s + offsetVec j ((5 * m : ℕ) : ℤ)) (6 * m) ⊆
      blockRegion lo i j m s ∧
    cubeAt (blockCentre lo i j m (s - (1, 0)) + offsetVec i ((5 * m : ℕ) : ℤ)) (6 * m) ⊆
      blockRegion lo i j m s ∧
    cubeAt (blockCentre lo i j m (s - (0, 1)) + offsetVec j ((5 * m : ℕ) : ℤ)) (6 * m) ⊆
      blockRegion lo i j m s := by
  rw [blockCentre_sub_i hij, blockCentre_sub_j hij]
  refine ⟨cubeAt_subset_blockRegion fun l => ?_, cubeAt_subset_blockRegion fun l => ?_,
    cubeAt_subset_blockRegion fun l => ?_, cubeAt_subset_blockRegion fun l => ?_,
    cubeAt_subset_blockRegion fun l => ?_⟩
  all_goals
    by_cases hli : l = i
    · subst hli
      simp [offsetVec_apply, hij]
      omega
    · by_cases hlj : l = j
      · subst hlj
        simp [offsetVec_apply, hli]
        omega
      · simp [offsetVec_apply, hli, hlj] <;> omega

/-- The good event of a block depends only on the bonds of its region. -/
theorem measurableSet_blockGood {lo : Vertex d} {i j : Fin d} (hij : i ≠ j) {m u n : ℕ}
    (hn : n ≤ 6 * m) (s : ℤ × ℤ) :
    MeasurableSet[localBondSigma (blockRegion lo i j m s)] (blockGood lo i j m u n s) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := blockGood_cubes_subset (lo := lo) hij hn s
  have hfin : ∀ (c : Vertex d) (r : ℕ), (cubeAt c r).Finite := fun c r => by
    rw [← coe_cubeFinset]
    exact Finset.finite_toSet _
  have hlink : ∀ (c : Vertex d) (a : Fin d),
      cubeAt (c + offsetVec a ((5 * m : ℕ) : ℤ)) (6 * m) ⊆ blockRegion lo i j m s →
        MeasurableSet[localBondSigma (blockRegion lo i j m s)] (linkEvent c a m u) := by
    intro c a hsub
    exact localBondSigma_mono hsub _ (measurableSet_connectsRegions_localBond _ _ _ (hfin _ _))
  refine MeasurableSet.inter (MeasurableSet.inter (MeasurableSet.inter (MeasurableSet.inter ?_
    (hlink _ _ h1)) (hlink _ _ h2)) (hlink _ _ h3)) (hlink _ _ h4)
  exact localBondSigma_mono h0 _ (measurableSet_uniqueZone_local _ _ _)

/-- Blocks at grid distance at least three have disjoint regions. -/
theorem disjoint_blockRegion {lo : Vertex d} {i j : Fin d} (hij : i ≠ j) {m : ℕ} (hm : 1 ≤ m)
    {s t : ℤ × ℤ} (h : LQGMetric.PercFar 2 s t) :
    Disjoint (blockRegion lo i j m s) (blockRegion lo i j m t) := by
  rw [Set.disjoint_left]
  intro v hs ht
  have hsi := abs_le.1 (hs i)
  have hti := abs_le.1 (ht i)
  have hsj := abs_le.1 (hs j)
  have htj := abs_le.1 (ht j)
  simp only [true_or, ↓reduceIte, blockCentre_apply_i] at hsi hti
  simp only [or_true, ↓reduceIte, blockCentre_apply_j hij] at hsj htj
  unfold LQGMetric.PercFar at h
  have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
  rcases h with h | h | h | h
  · have : (3 : ℤ) ≤ s.1 - t.1 := by push_cast at h; omega
    nlinarith
  · have : (3 : ℤ) ≤ t.1 - s.1 := by push_cast at h; omega
    nlinarith
  · have : (3 : ℤ) ≤ s.2 - t.2 := by push_cast at h; omega
    nlinarith
  · have : (3 : ℤ) ≤ t.2 - s.2 := by push_cast at h; omega
    nlinarith

/-- Boxes around centres at distance `10m` in a coordinate are far from each other. -/
theorem not_mem_cubeAt_of_offset {c c' : Vertex d} {k : Fin d} {m u n : ℕ}
    (hun : u + n < 10 * m)
    (hc : c' = c + offsetVec k ((10 * m : ℕ) : ℤ) ∨ c = c' + offsetVec k ((10 * m : ℕ) : ℤ))
    {y : Vertex d} (hy : y ∈ cubeAt c' u) : y ∉ cubeAt c n := by
  intro hyc
  have h1 := abs_le.1 (hy k)
  have h2 := abs_le.1 (hyc k)
  rcases hc with rfl | rfl <;> simp only [Pi.add_apply, offsetVec_apply, ↓reduceIte] at h1 h2 <;>
    push_cast at h1 h2 <;> omega

/-- A shell connection: the vertex is joined inside the cube to its shell. -/
def ShellConn (ω : Configuration d) (c : Vertex d) (n : ℕ) (y : Vertex d) : Prop :=
  ∃ v ∈ cubeShell c n, (openIn ω (cubeAt c n)).Reachable y v

/-- **Neighbouring good blocks are linked.** -/
theorem exists_link_of_adj {lo : Vertex d} {i j : Fin d} (hij : i ≠ j) {m u n : ℕ}
    (hun : u + n < 10 * m) (hu : u ≤ n) (hn : n ≤ 6 * m) {ω : Configuration d} {b c : ℤ × ℤ}
    (hb : ω ∈ blockGood lo i j m u n b) (hc : ω ∈ blockGood lo i j m u n c)
    (hadj : LQGMetric.PercAdj4 b c) :
    ∃ x ∈ cubeAt (blockCentre lo i j m b) u, ∃ y ∈ cubeAt (blockCentre lo i j m c) u,
      (∃ C, (C ⊆ blockRegion lo i j m b ∨ C ⊆ blockRegion lo i j m c) ∧
        (openIn ω C).Reachable x y) ∧
      ShellConn ω (blockCentre lo i j m b) n x ∧ ShellConn ω (blockCentre lo i j m c) n y := by
  obtain ⟨-, hb1, hb2, hb3, hb4⟩ := blockGood_cubes_subset (lo := lo) hij hn b
  obtain ⟨-, hc1, hc2, hc3, hc4⟩ := blockGood_cubes_subset (lo := lo) hij hn c
  obtain ⟨⟨⟨⟨-, lbi⟩, lbj⟩, lbi'⟩, lbj'⟩ := hb
  obtain ⟨⟨⟨⟨-, lci⟩, lcj⟩, lci'⟩, lcj'⟩ := hc
  -- a link from `p` to `q` with `zq = zp + 10m e_k` gives the conclusion in both orientations
  have key : ∀ (p q : ℤ × ℤ) (k : Fin d) (C : Set (Vertex d)),
      blockCentre lo i j m p + offsetVec k ((10 * m : ℕ) : ℤ) = blockCentre lo i j m q →
      ConnectsRegions ω C (cubeAt (blockCentre lo i j m p) u)
        (cubeAt (blockCentre lo i j m q) u) →
      ∃ x ∈ cubeAt (blockCentre lo i j m p) u, ∃ y ∈ cubeAt (blockCentre lo i j m q) u,
        (openIn ω C).Reachable x y ∧ ShellConn ω (blockCentre lo i j m p) n x ∧
          ShellConn ω (blockCentre lo i j m q) n y := by
    intro p q k C hpq hconn
    obtain ⟨x, -, hx, y, -, hy, hxy⟩ := hconn
    refine ⟨x, hx, y, hy, hxy, ?_, ?_⟩
    · exact exists_cubeShell_of_reachable hxy (cubeAt_mono hu hx)
        (not_mem_cubeAt_of_offset hun (Or.inl hpq.symm) hy)
    · exact exists_cubeShell_of_reachable hxy.symm (cubeAt_mono hu hy)
        (not_mem_cubeAt_of_offset hun (Or.inr hpq.symm) hx)
  unfold LQGMetric.PercAdj4 at hadj
  rcases hadj with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · -- `b = c + (0, 1)`
    have hbc : b = c + (0, 1) := Prod.ext (by simp [h1]) (by simp [h2])
    have hz : blockCentre lo i j m c + offsetVec j ((10 * m : ℕ) : ℤ) = blockCentre lo i j m b := by
      rw [hbc, blockCentre_add_j hij]
    have hlink : ConnectsRegions ω
        (cubeAt (blockCentre lo i j m c + offsetVec j ((5 * m : ℕ) : ℤ)) (6 * m))
        (cubeAt (blockCentre lo i j m c) u) (cubeAt (blockCentre lo i j m b) u) := by
      have := lcj
      unfold linkEvent at this
      rw [hz] at this
      exact this
    obtain ⟨x, hx, y, hy, hxy, sx, sy⟩ := key c b j _ hz hlink
    exact ⟨y, hy, x, hx, ⟨_, Or.inr hc2, hxy.symm⟩, sy, sx⟩
  · -- `c = b + (0, 1)`
    have hcb : c = b + (0, 1) := Prod.ext (by simp [h1]) (by simp [h2])
    have hz : blockCentre lo i j m b + offsetVec j ((10 * m : ℕ) : ℤ) = blockCentre lo i j m c := by
      rw [hcb, blockCentre_add_j hij]
    have hlink : ConnectsRegions ω
        (cubeAt (blockCentre lo i j m b + offsetVec j ((5 * m : ℕ) : ℤ)) (6 * m))
        (cubeAt (blockCentre lo i j m b) u) (cubeAt (blockCentre lo i j m c) u) := by
      have := lbj
      unfold linkEvent at this
      rw [hz] at this
      exact this
    obtain ⟨x, hx, y, hy, hxy, sx, sy⟩ := key b c j _ hz hlink
    exact ⟨x, hx, y, hy, ⟨_, Or.inl hb2, hxy⟩, sx, sy⟩
  · -- `b = c + (1, 0)`
    have hbc : b = c + (1, 0) := Prod.ext (by simp [h2]) (by simp [h1])
    have hz : blockCentre lo i j m c + offsetVec i ((10 * m : ℕ) : ℤ) = blockCentre lo i j m b := by
      rw [hbc, blockCentre_add_i hij]
    have hlink : ConnectsRegions ω
        (cubeAt (blockCentre lo i j m c + offsetVec i ((5 * m : ℕ) : ℤ)) (6 * m))
        (cubeAt (blockCentre lo i j m c) u) (cubeAt (blockCentre lo i j m b) u) := by
      have := lci
      unfold linkEvent at this
      rw [hz] at this
      exact this
    obtain ⟨x, hx, y, hy, hxy, sx, sy⟩ := key c b i _ hz hlink
    exact ⟨y, hy, x, hx, ⟨_, Or.inr hc1, hxy.symm⟩, sy, sx⟩
  · -- `c = b + (1, 0)`
    have hcb : c = b + (1, 0) := Prod.ext (by simp [h2]) (by simp [h1])
    have hz : blockCentre lo i j m b + offsetVec i ((10 * m : ℕ) : ℤ) = blockCentre lo i j m c := by
      rw [hcb, blockCentre_add_i hij]
    have hlink : ConnectsRegions ω
        (cubeAt (blockCentre lo i j m b + offsetVec i ((5 * m : ℕ) : ℤ)) (6 * m))
        (cubeAt (blockCentre lo i j m b) u) (cubeAt (blockCentre lo i j m c) u) := by
      have := lbi
      unfold linkEvent at this
      rw [hz] at this
      exact this
    obtain ⟨x, hx, y, hy, hxy, sx, sy⟩ := key b c i _ hz hlink
    exact ⟨x, hx, y, hy, ⟨_, Or.inl hb1, hxy⟩, sx, sy⟩

/-- **Chains of good blocks.** A good path of blocks inside the grid joins the boxes at its two
ends inside every region containing the regions of the blocks of the grid. -/
theorem connectsRegions_of_gridConn {lo : Vertex d} {i j : Fin d} (hij : i ≠ j) {m u n : ℕ}
    (hun : u + n < 10 * m) (hu : u ≤ n) (hn : n ≤ 6 * m) {K : ℤ} {Bx : Set (Vertex d)}
    (hreg : ∀ s, LQGMetric.percInGrid K K s → blockRegion lo i j m s ⊆ Bx) {ω : Configuration d}
    {a b : ℤ × ℤ} (h : GridConn K K {s | ω ∈ blockGood lo i j m u n s} a b) :
    ConnectsRegions ω Bx (cubeAt (blockCentre lo i j m a) u) (cubeAt (blockCentre lo i j m b) u) := by
  obtain ⟨ha, haG, hab⟩ := h
  have hcube : ∀ s, LQGMetric.percInGrid K K s → ∀ r, r ≤ 6 * m →
      cubeAt (blockCentre lo i j m s) r ⊆ Bx := fun s hs r hr =>
    ((blockGood_cubes_subset (lo := lo) hij hr s).1).trans (hreg s hs)
  have hmono : ∀ {C : Set (Vertex d)} {x y : Vertex d}, C ⊆ Bx → (openIn ω C).Reachable x y →
      (openIn ω Bx).Reachable x y := fun hC hxy => openIn_reachable_mono_region hC hxy
  have hQ : b = a ∨ ∃ x ∈ cubeAt (blockCentre lo i j m a) u,
      ∃ y ∈ cubeAt (blockCentre lo i j m b) u,
        (openIn ω Bx).Reachable x y ∧ ShellConn ω (blockCentre lo i j m b) n y := by
    induction hab with
    | refl => exact Or.inl rfl
    | @tail b c _ hbc ih =>
      obtain ⟨hbg, hbG, hcg, hcG, hadj⟩ := hbc
      obtain ⟨x', hx', y', hy', ⟨C, hC, hxy'⟩, sx', sy'⟩ :=
        exists_link_of_adj hij hun hu hn hbG hcG hadj
      have hCB : C ⊆ Bx := by
        rcases hC with hC | hC
        · exact hC.trans (hreg b hbg)
        · exact hC.trans (hreg c hcg)
      right
      rcases ih with rfl | ⟨x, hx, y, hy, hxy, sy⟩
      · exact ⟨x', hx', y', hy', hmono hCB hxy', sy'⟩
      · have hU : UniqueZone ω (blockCentre lo i j m b) u n := hbG.1.1.1.1
        have hyx' := hU y hy x' hx' sy sx'
        exact ⟨x, hx, y', hy', (hxy.trans (hmono (hcube b hbg n hn) hyx')).trans
          (hmono hCB hxy'), sy'⟩
  have hzmem : ∀ s, LQGMetric.percInGrid K K s → blockCentre lo i j m s ∈ cubeAt
      (blockCentre lo i j m s) u := fun s _ k => by simp
  have hbg : LQGMetric.percInGrid K K b := (GridConn.mem ⟨ha, haG, hab⟩).1
  rcases hQ with rfl | ⟨x, hx, y, hy, hxy, -⟩
  · exact ⟨_, hcube b hbg 0 (by omega) (fun k => by simp), hzmem b hbg, _,
      hcube b hbg 0 (by omega) (fun k => by simp), hzmem b hbg, SimpleGraph.Reachable.refl _⟩
  · exact ⟨x, hcube a ha u (by omega) hx, hx, y, hcube b hbg u (by omega) hy, hy, hxy⟩

end Rigidity.Percolation
