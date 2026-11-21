import Rigidity.Percolation.Blocks.SlabBlocks

/-!
# Two-point connections in slab boxes

Above criticality there are a thickness `w` and a constant `ρ > 0` such that any two vertices of
any slab box with two long sides of length at least `22m + 1` and thin sides `w` are joined inside
the box with probability at least `ρ`. Each vertex is joined by a short path to every vertex of a
nearby block box with probability bounded below, and the boxes of the two nearby blocks are
joined with probability at least one half by a chain of good blocks; Harris' inequality combines
the three increasing events.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped ENNReal

variable {d : ℕ}

/-- The number of vertices of a finite cube. -/
theorem card_cubeFinset (c : Vertex d) (r : ℕ) : (cubeFinset c r).card = (2 * r + 1) ^ d := by
  simp only [cubeFinset, Fintype.card_piFinset, Int.card_Icc]
  rw [Finset.prod_congr rfl (fun x _ => show (c x + (r : ℤ) + 1 - (c x - r)).toNat = 2 * r + 1 by
    omega), Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The number of blocks per side of the grid of a slab box. -/
def gridSide (S m : ℕ) : ℕ := (S - 1 - 22 * m) / (10 * m) + 1

theorem gridSide_mul_le {S m : ℕ} :
    10 * m * (gridSide S m - 1) ≤ S - 1 - 22 * m := by
  show 10 * m * ((S - 1 - 22 * m) / (10 * m) + 1 - 1) ≤ S - 1 - 22 * m
  rw [Nat.add_sub_cancel, Nat.mul_comm]
  exact Nat.div_mul_le_self _ _

theorem lt_gridSide_mul {S m : ℕ} (hm : 1 ≤ m) :
    S - 1 - 22 * m < 10 * m * (gridSide S m - 1) + 10 * m := by
  show S - 1 - 22 * m < 10 * m * ((S - 1 - 22 * m) / (10 * m) + 1 - 1) + 10 * m
  rw [Nat.add_sub_cancel, Nat.mul_comm (10 * m)]
  exact Nat.lt_div_mul_add (by omega)

/-- The regions of the blocks of the grid lie in the slab box. -/
theorem blockRegion_subset_slabBox {lo : Vertex d} {i j : Fin d} (hij : i ≠ j) {m S : ℕ}
    (hm : 1 ≤ m) (hS : 22 * m + 1 ≤ S) {s : ℤ × ℤ}
    (hs : LQGMetric.percInGrid (gridSide S m) (gridSide S m) s) :
    blockRegion lo i j m s ⊆ slabBox lo i j S (12 * m + 1) := by
  have hK := gridSide_mul_le (S := S) (m := m)
  have hK1 : 1 ≤ gridSide S m := by simp [gridSide]
  unfold LQGMetric.percInGrid at hs
  have hK' : (10 * m : ℤ) * ((gridSide S m : ℤ) - 1) ≤ S - 1 - 22 * m := by
    have : ((10 * m * (gridSide S m - 1) : ℕ) : ℤ) ≤ ((S - 1 - 22 * m : ℕ) : ℤ) :=
      by exact_mod_cast hK
    push_cast [Nat.cast_sub hK1, Nat.cast_sub (by omega : 22 * m ≤ S - 1),
      Nat.cast_sub (by omega : 1 ≤ S)] at this
    linarith
  have h1 : 0 ≤ (10 * m : ℤ) * s.1 := mul_nonneg (by positivity) (by omega)
  have h2 : 0 ≤ (10 * m : ℤ) * s.2 := mul_nonneg (by positivity) (by omega)
  have h3 : (10 * m : ℤ) * s.1 ≤ (10 * m : ℤ) * ((gridSide S m : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left (by omega) (by positivity)
  have h4 : (10 * m : ℤ) * s.2 ≤ (10 * m : ℤ) * ((gridSide S m : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left (by omega) (by positivity)
  intro v hv l
  have hvl := abs_le.1 (hv l)
  by_cases hli : l = i
  · subst hli
    simp only [true_or, ↓reduceIte, blockCentre_apply_i] at hvl ⊢
    constructor <;> linarith [hvl.1, hvl.2]
  · by_cases hlj : l = j
    · subst hlj
      simp only [or_true, ↓reduceIte, blockCentre_apply_j hij] at hvl ⊢
      constructor <;> linarith [hvl.1, hvl.2]
    · simp only [hli, hlj, or_self, ↓reduceIte, blockCentre_apply_other hli hlj] at hvl ⊢
      push_cast
      constructor <;> linarith [hvl.1, hvl.2]

/-- Every position along a long side is within `21m` of a block centre of the grid. -/
theorem exists_index_near {q S m : ℕ} (hm : 1 ≤ m) (hS : 22 * m + 1 ≤ S) (hq : q < S) :
    ∃ t : ℕ, t < gridSide S m ∧ |(q : ℤ) - (11 * m + 10 * m * t)| ≤ 21 * m := by
  have hA := Nat.div_mul_le_self q (10 * m)
  have hA' := Nat.lt_div_mul_add (a := q) (show 0 < 10 * m by omega)
  have hB := gridSide_mul_le (S := S) (m := m)
  have hB' := lt_gridSide_mul (S := S) hm
  have hK1 : 1 ≤ gridSide S m := by simp [gridSide]
  by_cases hk : q / (10 * m) ≤ gridSide S m - 1
  · refine ⟨q / (10 * m), by omega, ?_⟩
    rw [abs_le]
    have e : (q / (10 * m) * (10 * m) : ℕ) = 10 * m * (q / (10 * m)) := Nat.mul_comm _ _
    constructor <;> push_cast at hA hA' e ⊢ <;> nlinarith
  · push Not at hk
    refine ⟨gridSide S m - 1, by omega, ?_⟩
    have hmono : 10 * m * gridSide S m ≤ 10 * m * (q / (10 * m)) :=
      Nat.mul_le_mul_left _ (by omega)
    have e : (q / (10 * m) * (10 * m) : ℕ) = 10 * m * (q / (10 * m)) := Nat.mul_comm _ _
    have e2 : 10 * m * gridSide S m = 10 * m * (gridSide S m - 1) + 10 * m := by
      rw [← Nat.mul_succ]
      congr 1
    rw [abs_le]
    have hcast : ((gridSide S m - 1 : ℕ) : ℤ) = (gridSide S m : ℤ) - 1 := by push_cast [hK1]; ring
    rw [hcast]
    have hB2 : (10 * m * (gridSide S m - 1) : ℕ) ≤ S - 1 - 22 * m := hB
    zify [hK1, (by omega : 22 * m ≤ S - 1), (by omega : 1 ≤ S)] at hA hA' hB hB' hmono e e2
    constructor <;> nlinarith

/-- The slab box is a lattice rectangle. -/
theorem slabBox_eq_latticeRectangle (lo : Vertex d) (i j : Fin d) (S w : ℕ) :
    slabBox lo i j S w =
      latticeRectangle lo (fun l => lo l + if l = i ∨ l = j then (S : ℤ) else w) := rfl

/-- **Short connections.** A vertex of a lattice rectangle within distance `R` of a centre whose
box of radius `u ≤ R` lies in the rectangle is joined inside the rectangle to every vertex of the
box with probability at least `(p^{(2R+1)^d})^{(2u+1)^d}`. -/
theorem pow_le_prob_reach_box (p : unitInterval) {lo hi x c : Vertex d} {R u : ℕ}
    (hx : x ∈ latticeRectangle lo hi) (hxc : x ∈ cubeAt c R)
    (hcu : cubeAt c u ⊆ latticeRectangle lo hi) (huR : u ≤ R) :
    ((p : ℝ) ^ ((2 * R + 1) ^ d)) ^ ((2 * u + 1) ^ d) ≤ (latticeBondLaw d p).real
      (⋂ v ∈ cubeFinset c u, {ω | (openIn ω (latticeRectangle lo hi)).Reachable x v}) := by
  classical
  set F := (cubeFinset c R).filter (· ∈ latticeRectangle lo hi) with hF
  have hFrect : ((F : Finset (Vertex d)) : Set (Vertex d)) =
      latticeRectangle (fun l => max (lo l) (c l - R)) (fun l => min (hi l) (c l + R + 1)) := by
    ext z
    simp only [hF, Finset.coe_filter, mem_cubeFinset, mem_cubeAt, latticeRectangle,
      Set.mem_setOf_eq, abs_le]
    constructor
    · rintro ⟨h1, h2⟩ l
      have := h1 l
      have := h2 l
      constructor <;> omega
    · intro h
      exact ⟨fun l => by have := h l; constructor <;> omega, fun l => by have := h l; omega⟩
  have hFcard : F.card ≤ (2 * R + 1) ^ d :=
    (Finset.card_filter_le _ _).trans (card_cubeFinset c R).le
  have hxF : x ∈ F := Finset.mem_filter.2 ⟨mem_cubeFinset.2 hxc, hx⟩
  have hp0 : (0 : ℝ) ≤ p := p.property.1
  have hp1 : (p : ℝ) ≤ 1 := p.property.2
  have hone : ∀ v ∈ cubeFinset c u, (p : ℝ) ^ ((2 * R + 1) ^ d) ≤
      (latticeBondLaw d p).real {ω | (openIn ω (latticeRectangle lo hi)).Reachable x v} := by
    intro v hv
    have hvc := mem_cubeFinset.1 hv
    have hvF : v ∈ F := Finset.mem_filter.2 ⟨mem_cubeFinset.2 (cubeAt_mono huR hvc), hcu hvc⟩
    have hpath : (openIn (allOpen d) (F : Set (Vertex d))).Reachable x v := by
      rw [hFrect]
      have hx' : x ∈ latticeRectangle (fun l => max (lo l) (c l - R))
          (fun l => min (hi l) (c l + R + 1)) := by rw [← hFrect]; exact hxF
      have hv' : v ∈ latticeRectangle (fun l => max (lo l) (c l - R))
          (fun l => min (hi l) (c l + R + 1)) := by rw [← hFrect]; exact hvF
      exact reachable_allOpen_latticeRectangle _ _ hx' hv'
    have h1 := pow_card_le_measureReal_reachable_openIn p F hxF hpath
    have hsub : {ω : Configuration d | (openIn ω (F : Set (Vertex d))).Reachable x v} ⊆
        {ω | (openIn ω (latticeRectangle lo hi)).Reachable x v} := fun ω hω =>
      openIn_reachable_mono_region (fun z hz => (Finset.mem_filter.1 hz).2) hω
    calc (p : ℝ) ^ ((2 * R + 1) ^ d) ≤ (p : ℝ) ^ F.card := pow_le_pow_of_le_one hp0 hp1 hFcard
      _ ≤ _ := h1
      _ ≤ _ := measureReal_mono hsub
  calc ((p : ℝ) ^ ((2 * R + 1) ^ d)) ^ ((2 * u + 1) ^ d)
      = ∏ _v ∈ cubeFinset c u, (p : ℝ) ^ ((2 * R + 1) ^ d) := by
        rw [Finset.prod_const, card_cubeFinset]
    _ ≤ ∏ v ∈ cubeFinset c u,
        (latticeBondLaw d p).real {ω | (openIn ω (latticeRectangle lo hi)).Reachable x v} :=
        Finset.prod_le_prod (fun _ _ => by positivity) hone
    _ ≤ _ := prod_le_latticeBondLaw_real_biInter p _
        (fun v => isUpperSet_reachable_openIn _ x v) (fun v => measurableSet_openIn_reachable _ x v)
        (cubeFinset c u)

/-- Every vertex of a slab box is within `21m` of a block centre of the grid. -/
theorem exists_block_near {lo : Vertex d} {i j : Fin d} (hij : i ≠ j) {m S : ℕ} (hm : 1 ≤ m)
    (hS : 22 * m + 1 ≤ S) {x : Vertex d} (hx : x ∈ slabBox lo i j S (12 * m + 1)) :
    ∃ s, LQGMetric.percInGrid (gridSide S m) (gridSide S m) s ∧
      x ∈ cubeAt (blockCentre lo i j m s) (21 * m) := by
  have hxi := hx i
  have hxj := hx j
  simp only [true_or, or_true, ↓reduceIte] at hxi hxj
  obtain ⟨ti, hti, hi⟩ := exists_index_near (q := (x i - lo i).toNat) hm hS (by omega)
  obtain ⟨tj, htj, hj⟩ := exists_index_near (q := (x j - lo j).toNat) hm hS (by omega)
  refine ⟨((ti : ℤ), (tj : ℤ)), ?_, fun l => ?_⟩
  · unfold LQGMetric.percInGrid
    simp only
    omega
  · by_cases hli : l = i
    · subst hli
      rw [blockCentre_apply_i]
      have : ((x l - lo l).toNat : ℤ) = x l - lo l := Int.toNat_of_nonneg (by omega)
      rw [this] at hi
      push_cast
      convert hi using 2
      ring
    · by_cases hlj : l = j
      · subst hlj
        rw [blockCentre_apply_j hij]
        have : ((x l - lo l).toNat : ℤ) = x l - lo l := Int.toNat_of_nonneg (by omega)
        rw [this] at hj
        push_cast
        convert hj using 2
        ring
      · rw [blockCentre_apply_other hli hlj]
        have := hx l
        simp only [hli, hlj, or_self, ↓reduceIte] at this
        push_cast at this ⊢
        rw [abs_le]
        constructor <;> omega

/-- A bad block probability bound gives the hypotheses of the Peierls bound for the blocks. -/
theorem peierlsHyp_blocks (p : unitInterval) {lo : Vertex d} {i j : Fin d} (hij : i ≠ j)
    {m u n : ℕ} (hm : 1 ≤ m) (hn : n ≤ 6 * m) (K : ℤ) {ε : ℝ}
    (hbad : ∀ s, (latticeBondLaw d p).real (blockGood lo i j m u n s)ᶜ ≤ ε) :
    PeierlsHyp (latticeBondLaw d p) K K (fun s => (blockGood lo i j m u n s)ᶜ) 2
      (ENNReal.ofReal ε) := by
  refine ⟨fun s _ => ?_, fun F _ hfar => ?_⟩
  · rw [← ENNReal.ofReal_toReal (measure_ne_top (latticeBondLaw d p) _)]
    exact ENNReal.ofReal_le_ofReal (hbad s)
  · refine le_of_eq (latticeBondLaw_biInter_eq_prod p (blockRegion lo i j m)
      (fun s => (blockGood lo i j m u n s)ᶜ) (fun s => (measurableSet_blockGood hij hn s).compl)
      F ?_)
    intro s hs t ht hst
    exact disjoint_blockRegion hij hm (hfar s hs t ht hst)

/-- **Two-point connections in slab boxes.** Above criticality in dimension at least two there
are a scale `m ≥ 1` and `ρ > 0` such that any two vertices of any slab box with long sides
`S ≥ 22m + 1` and thin sides `12m + 1` are joined inside the box with probability at least `ρ`. -/
theorem exists_slabBox_two_point [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hp : criticalProbability d < (p : ℝ)) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ (lo : Vertex d) (i j : Fin d), i ≠ j → ∀ S : ℕ,
      22 * m + 1 ≤ S → ∀ x ∈ slabBox lo i j S (12 * m + 1), ∀ y ∈ slabBox lo i j S (12 * m + 1),
        ρ ≤ (latticeBondLaw d p).real
          {ω | (openIn ω (slabBox lo i j S (12 * m + 1))).Reachable x y} := by
  classical
  set η : ℝ := (1 / 128 : ℝ) ^ 9 / 5 with hηdef
  have hη : 0 < η := by positivity
  have hab : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by
    intro h
    simp [Fin.ext_iff] at h
  obtain ⟨u, hlink⟩ := exists_link_scale hab hp hη
  obtain ⟨nU, hU⟩ := exists_uniqueZone_prob (d := d) p u hη
  set n := nU + u with hn
  obtain ⟨m, hNm, -, hlinks⟩ := hlink (n + u + 1)
  have hm : 1 ≤ m := by omega
  have hun : u + n < 10 * m := by omega
  have hnm : n ≤ 6 * m := by omega
  have hp0 : 0 < (p : ℝ) := lt_of_le_of_lt (criticalProbability_nonneg d) hp
  set R := 21 * m with hR
  set c₀ : ℝ := ((p : ℝ) ^ ((2 * R + 1) ^ d)) ^ ((2 * u + 1) ^ d) with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  refine ⟨m, hm, c₀ * c₀ * (1 / 2), by positivity, ?_⟩
  intro lo i j hij S hS x hx y hy
  set μ := latticeBondLaw d p with hμ
  set Bx := slabBox lo i j S (12 * m + 1) with hBx
  set K := gridSide S m with hK
  have hK1 : 1 ≤ K := by simp [hK, gridSide]
  have hreg : ∀ s, LQGMetric.percInGrid (K : ℤ) K s → blockRegion lo i j m s ⊆ Bx :=
    fun s hs => blockRegion_subset_slabBox hij hm hS hs
  obtain ⟨sx, hsx, hxz⟩ := exists_block_near hij hm hS hx
  obtain ⟨sy, hsy, hyz⟩ := exists_block_near hij hm hS hy
  -- bad blocks are rare
  have hbad : ∀ s, μ.real (blockGood lo i j m u n s)ᶜ ≤ 5 * η := by
    intro s
    have hsub : (blockGood lo i j m u n s)ᶜ ⊆
        ((({ω | UniqueZone ω (blockCentre lo i j m s) u n}ᶜ ∪
          (linkEvent (blockCentre lo i j m s) i m u)ᶜ) ∪
          (linkEvent (blockCentre lo i j m s) j m u)ᶜ) ∪
          (linkEvent (blockCentre lo i j m (s - (1, 0))) i m u)ᶜ) ∪
          (linkEvent (blockCentre lo i j m (s - (0, 1))) j m u)ᶜ := by
      intro ω hω
      simp only [blockGood, Set.mem_compl_iff, Set.mem_inter_iff, not_and_or] at hω
      simp only [Set.mem_union, Set.mem_compl_iff]
      tauto
    have hcompl : ∀ A : Set (Configuration d), MeasurableSet A → 1 - η ≤ μ.real A →
        μ.real Aᶜ ≤ η := fun A hA h => by
      rw [measureReal_compl hA, probReal_univ]
      linarith
    have hl : ∀ (c : Vertex d) (b : Fin d), μ.real (linkEvent c b m u)ᶜ ≤ η := fun c b =>
      hcompl _ (measurableSet_connectsRegions _ _ _) (hlinks c b)
    have hu : μ.real {ω | UniqueZone ω (blockCentre lo i j m s) u n}ᶜ ≤ η :=
      hcompl _ (measurableSet_uniqueZone _ _ _) (hU n (by omega) _).le
    calc _ ≤ _ := measureReal_mono hsub
      _ ≤ _ := (measureReal_union_le _ _).trans (add_le_add ((measureReal_union_le _ _).trans
          (add_le_add ((measureReal_union_le _ _).trans (add_le_add
          (measureReal_union_le _ _) le_rfl)) le_rfl)) le_rfl)
      _ ≤ 5 * η := by
          linarith [hu, hl (blockCentre lo i j m s) i, hl (blockCentre lo i j m s) j,
            hl (blockCentre lo i j m (s - (1, 0))) i, hl (blockCentre lo i j m (s - (0, 1))) j]
  -- the chain of good blocks
  have hPH := peierlsHyp_blocks p hij hm hnm (K : ℤ) hbad
  have hε : ENNReal.ofReal (5 * η) ≤ (128 : ℝ≥0∞)⁻¹ ^ ((2 + 1) ^ 2) := by
    have : 5 * η = ((128 : ℝ)⁻¹) ^ 9 := by rw [hηdef]; norm_num
    rw [this, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hgrid := gridConn_prob_le hε (n₀ := 5) (by norm_num) (n := K) le_rfl (by omega) le_rfl
    (by omega) (by exact_mod_cast hK1) (by exact_mod_cast hK1) hPH hsx hsy
  have htoReal : (ENNReal.ofReal (5 * η)).toReal = 5 * η := ENNReal.toReal_ofReal (by positivity)
  rw [htoReal] at hgrid
  set C := {ω : Configuration d | ConnectsRegions ω Bx (cubeAt (blockCentre lo i j m sx) u)
    (cubeAt (blockCentre lo i j m sy) u)} with hC
  have hCm : MeasurableSet C := measurableSet_connectsRegions _ _ _
  have hGC : {ω : Configuration d | GridConn K K {s | ω ∉ (blockGood lo i j m u n s)ᶜ} sx sy} ⊆
      C := by
    intro ω hω
    have hω' : GridConn K K {s | ω ∈ blockGood lo i j m u n s} sx sy := by
      simpa only [Set.mem_setOf_eq, Set.mem_compl_iff, not_not] using hω
    exact connectsRegions_of_gridConn hij hun (by omega) hnm hreg hω'
  have hC_half : 1 / 2 ≤ μ.real C := by
    have h1 : 1 ≤ μ.real {ω : Configuration d |
        GridConn K K {s | ω ∉ (blockGood lo i j m u n s)ᶜ} sx sy} +
        μ.real {ω : Configuration d |
        ¬ GridConn K K {s | ω ∉ (blockGood lo i j m u n s)ᶜ} sx sy} := by
      have := measureReal_union_le (μ := μ) {ω : Configuration d |
        GridConn K K {s | ω ∉ (blockGood lo i j m u n s)ᶜ} sx sy}
        {ω | ¬ GridConn K K {s | ω ∉ (blockGood lo i j m u n s)ᶜ} sx sy}
      rw [Set.union_def] at this
      simp only [Set.mem_setOf_eq, em, Set.setOf_true, probReal_univ] at this
      exact this
    have h2 := measureReal_mono (μ := μ) hGC
    have h3 : (2 : ℝ) * (((5 + 1 : ℕ) ^ 2 : ℝ) * (5 * η) + 4 * (1 / 2 : ℝ) ^ 5) ≤ 1 / 2 := by
      rw [hηdef]
      norm_num
    linarith
  -- short connections at the two ends
  have hcube : ∀ s, LQGMetric.percInGrid (K : ℤ) K s →
      cubeAt (blockCentre lo i j m s) u ⊆ Bx := fun s hs =>
    ((blockGood_cubes_subset (lo := lo) hij (by omega : u ≤ 6 * m) s).1).trans (hreg s hs)
  set Ex := ⋂ v ∈ cubeFinset (blockCentre lo i j m sx) u, {ω : Configuration d |
    (openIn ω Bx).Reachable x v} with hEx
  set Ey := ⋂ v ∈ cubeFinset (blockCentre lo i j m sy) u, {ω : Configuration d |
    (openIn ω Bx).Reachable y v} with hEy
  have hEx_le : c₀ ≤ μ.real Ex :=
    pow_le_prob_reach_box (lo := lo)
      (hi := fun l => lo l + if l = i ∨ l = j then (S : ℤ) else ((12 * m + 1 : ℕ) : ℤ))
      p hx hxz (hcube sx hsx) (by omega)
  have hEy_le : c₀ ≤ μ.real Ey :=
    pow_le_prob_reach_box (lo := lo)
      (hi := fun l => lo l + if l = i ∨ l = j then (S : ℤ) else ((12 * m + 1 : ℕ) : ℤ))
      p hy hyz (hcube sy hsy) (by omega)
  have hExm : MeasurableSet Ex :=
    Finset.measurableSet_biInter _ fun v _ => measurableSet_openIn_reachable _ _ _
  have hEym : MeasurableSet Ey :=
    Finset.measurableSet_biInter _ fun v _ => measurableSet_openIn_reachable _ _ _
  have hExu : IsUpperSet Ex := isUpperSet_iInter₂ fun v _ => isUpperSet_reachable_openIn _ _ _
  have hEyu : IsUpperSet Ey := isUpperSet_iInter₂ fun v _ => isUpperSet_reachable_openIn _ _ _
  have hCu : IsUpperSet C := isUpperSet_connectsRegions _ _ _
  have hharris1 := LatticeProb.infinitePi_harris_bool (fun _ : Bond d =>
    bernoulliMeasure true false p) hExu hEyu hExm hEym
  have hharris2 := LatticeProb.infinitePi_harris_bool (fun _ : Bond d =>
    bernoulliMeasure true false p) (hExu.inter hEyu) hCu (hExm.inter hEym) hCm
  change μ.real Ex * μ.real Ey ≤ μ.real (Ex ∩ Ey) at hharris1
  change μ.real (Ex ∩ Ey) * μ.real C ≤ μ.real (Ex ∩ Ey ∩ C) at hharris2
  have hsub : Ex ∩ Ey ∩ C ⊆ {ω | (openIn ω Bx).Reachable x y} := by
    rintro ω ⟨⟨hωx, hωy⟩, ⟨v, -, hv, v', -, hv', hvv'⟩⟩
    have h1 : (openIn ω Bx).Reachable x v :=
      Set.mem_iInter₂.1 hωx v (mem_cubeFinset.2 hv)
    have h2 : (openIn ω Bx).Reachable y v' :=
      Set.mem_iInter₂.1 hωy v' (mem_cubeFinset.2 hv')
    exact (h1.trans hvv').trans h2.symm
  have hfinal := measureReal_mono (μ := μ) hsub
  have hEE : c₀ * c₀ ≤ μ.real (Ex ∩ Ey) :=
    (mul_le_mul hEx_le hEy_le hc₀pos.le measureReal_nonneg).trans hharris1
  calc c₀ * c₀ * (1 / 2) ≤ μ.real (Ex ∩ Ey) * μ.real C :=
        mul_le_mul hEE hC_half (by norm_num) measureReal_nonneg
    _ ≤ μ.real (Ex ∩ Ey ∩ C) := hharris2
    _ ≤ _ := hfinal

end Rigidity.Percolation
