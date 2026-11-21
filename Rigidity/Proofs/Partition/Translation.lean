import Rigidity.Proofs.Partition.PartitionCube
import Rigidity.Proofs.Percolation.TriadicCappedPartition
import LatticeProb.Prob.Percolation.OpenGraphTranslation

/-!
# Translations of well-connected cubes, good cubes and anchors

Translating a configuration by `c` moves its open graph by `c`, and with it open connections
inside regions, crossing roots, crossable regions and connections of selected paths. For a triadic
cube `Q` whose side divides every coordinate of `c`, the shifted cube `Q.shift c` is the translate
of `Q`; it is well-connected, good, has crossing cluster and anchor in the translated configuration
exactly when `Q` does in the original one, translated by `c`. For `c ∈ 3ⁿ ℤᵈ` the partition into
good cubes capped at scale `n` moves with the translation.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

variable {d : ℕ}

/-- `A'` is the translate of `A` by `c`. -/
def IsTranslate (c : Vertex d) (A A' : Set (Vertex d)) : Prop :=
  ∀ v, v + c ∈ A' ↔ v ∈ A

theorem IsTranslate.sub_mem_iff {c : Vertex d} {A A' : Set (Vertex d)} (h : IsTranslate c A A')
    (v : Vertex d) : v - c ∈ A ↔ v ∈ A' := by
  rw [← h, sub_add_cancel]

/-- Translation by `c` is an isomorphism of the open graphs inside a region and inside its
translate. -/
def openInTranslation (c : Vertex d) (ω : Configuration d) {S S' : Set (Vertex d)}
    (hS : IsTranslate c S S') :
    openIn ω S ≃g openIn (configurationTranslation c ω) S' where
  toFun x := x + c
  invFun x := x - c
  left_inv x := add_sub_cancel_right x c
  right_inv x := sub_add_cancel x c
  map_rel_iff' := by
    intro a b
    change (openGraph (configurationTranslation c ω)).Adj (a + c) (b + c) ∧ a + c ∈ S' ∧
      b + c ∈ S' ↔ (openGraph ω).Adj a b ∧ a ∈ S ∧ b ∈ S
    rw [openGraph_adj_translation_iff, hS, hS]

/-- Open edges inside a region move with a translation of the configuration. -/
theorem openIn_adj_translation_iff (c : Vertex d) (ω : Configuration d) {S S' : Set (Vertex d)}
    (hS : IsTranslate c S S') (x y : Vertex d) :
    (openIn (configurationTranslation c ω) S').Adj (x + c) (y + c) ↔ (openIn ω S).Adj x y :=
  (openInTranslation c ω hS).map_rel_iff

/-- Open connections inside a region move with a translation of the configuration. -/
theorem openIn_reachable_translation_iff (c : Vertex d) (ω : Configuration d)
    {S S' : Set (Vertex d)} (hS : IsTranslate c S S') (x y : Vertex d) :
    (openIn (configurationTranslation c ω) S').Reachable (x + c) (y + c) ↔
      (openIn ω S).Reachable x y :=
  (openInTranslation c ω hS).reachable_iff

theorem openIn_reachable_translation_sub_iff (c : Vertex d) (ω : Configuration d)
    {S S' : Set (Vertex d)} (hS : IsTranslate c S S') (x y : Vertex d) :
    (openIn (configurationTranslation c ω) S').Reachable x y ↔
      (openIn ω S).Reachable (x - c) (y - c) := by
  rw [← openIn_reachable_translation_iff c ω hS, sub_add_cancel, sub_add_cancel]

/-- Crossing roots move with a translation of the configuration. -/
theorem isCrossingRoot_translation_iff (c : Vertex d) (ω : Configuration d)
    {B B' : Set (Vertex d)} {lower upper lower' upper' : Fin d → Set (Vertex d)}
    (hB : IsTranslate c B B') (hl : ∀ i, IsTranslate c (lower i) (lower' i))
    (hu : ∀ i, IsTranslate c (upper i) (upper' i)) (r : Vertex d) :
    IsCrossingRoot (configurationTranslation c ω) B' lower' upper' (r + c) ↔
      IsCrossingRoot ω B lower upper r := by
  unfold IsCrossingRoot
  rw [hB r]
  refine and_congr Iff.rfl (forall_congr' fun i => and_congr ?_ ?_)
  · constructor
    · rintro ⟨y, hyB, hyl, hry⟩
      refine ⟨y - c, (hB.sub_mem_iff y).2 hyB, ((hl i).sub_mem_iff y).2 hyl, ?_⟩
      rwa [openIn_reachable_translation_sub_iff c ω hB, add_sub_cancel_right] at hry
    · rintro ⟨y, hyB, hyl, hry⟩
      exact ⟨y + c, (hB y).2 hyB, (hl i y).2 hyl, (openIn_reachable_translation_iff c ω hB r y).2 hry⟩
  · constructor
    · rintro ⟨y, hyB, hyu, hry⟩
      refine ⟨y - c, (hB.sub_mem_iff y).2 hyB, ((hu i).sub_mem_iff y).2 hyu, ?_⟩
      rwa [openIn_reachable_translation_sub_iff c ω hB, add_sub_cancel_right] at hry
    · rintro ⟨y, hyB, hyu, hry⟩
      exact ⟨y + c, (hB y).2 hyB, (hu i y).2 hyu, (openIn_reachable_translation_iff c ω hB r y).2 hry⟩

/-- Crossability moves with a translation of the configuration. -/
theorem crossableRegion_translation_iff (c : Vertex d) (ω : Configuration d)
    {B B' : Set (Vertex d)} {lower upper lower' upper' : Fin d → Set (Vertex d)}
    (hB : IsTranslate c B B') (hl : ∀ i, IsTranslate c (lower i) (lower' i))
    (hu : ∀ i, IsTranslate c (upper i) (upper' i)) :
    CrossableRegion (configurationTranslation c ω) B' lower' upper' ↔
      CrossableRegion ω B lower upper := by
  unfold CrossableRegion
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨x, hxB, y, hyB, hxl, hyu, hxy⟩
    refine ⟨x - c, (hB.sub_mem_iff x).2 hxB, y - c, (hB.sub_mem_iff y).2 hyB,
      ((hl i).sub_mem_iff x).2 hxl, ((hu i).sub_mem_iff y).2 hyu, ?_⟩
    rwa [openIn_reachable_translation_sub_iff c ω hB] at hxy
  · rintro ⟨x, hxB, y, hyB, hxl, hyu, hxy⟩
    exact ⟨x + c, (hB x).2 hxB, y + c, (hB y).2 hyB, (hl i x).2 hxl, (hu i y).2 hyu,
      (openIn_reachable_translation_iff c ω hB x y).2 hxy⟩

/-- Connections of selected paths move with a translation of the configuration. -/
theorem connectsSelectedPaths_translation_iff (c : Vertex d) (ω : Configuration d)
    {B B' C C' : Set (Vertex d)} (hB : IsTranslate c B B') (hC : IsTranslate c C C')
    {large large' : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop}
    (hlarge : ∀ n γ, large' n (fun j => γ j + c) ↔ large n γ) (r : Vertex d) :
    ConnectsSelectedPaths (configurationTranslation c ω) B' C' (r + c) large' ↔
      ConnectsSelectedPaths ω B C r large := by
  unfold ConnectsSelectedPaths
  constructor
  · intro h n γ hγ h0 hadj
    obtain ⟨z, hzB, hγz, hrz⟩ := h n (fun j => γ j + c) ((hlarge n γ).2 hγ) ((hB _).2 h0)
      (fun i => (openIn_adj_translation_iff c ω hB _ _).2 (hadj i))
    refine ⟨z - c, (hB.sub_mem_iff z).2 hzB, ?_, ?_⟩
    · rwa [openIn_reachable_translation_sub_iff c ω hB, add_sub_cancel_right] at hγz
    · rwa [openIn_reachable_translation_sub_iff c ω hC, add_sub_cancel_right] at hrz
  · intro h n γ hγ h0 hadj
    obtain ⟨z, hzB, hγz, hrz⟩ := h n (fun j => γ j - c)
      ((hlarge n _).1 (by simpa only [sub_add_cancel] using hγ))
      ((hB.sub_mem_iff _).2 h0) (fun i => by
        rw [← openIn_adj_translation_iff c ω hB, sub_add_cancel, sub_add_cancel]
        exact hadj i)
    refine ⟨z + c, (hB z).2 hzB, ?_, (openIn_reachable_translation_iff c ω hC r z).2 hrz⟩
    have h1 := (openIn_reachable_translation_iff c ω hB (γ 0 - c) z).2 hγz
    rwa [sub_add_cancel] at h1

/-- The integer cube moved by `c`. -/
def IntegerCube.shift (R : IntegerCube d) (c : Vertex d) : IntegerCube d :=
  ⟨R.corner + c, R.size⟩

theorem IntegerCube.isTranslate_shift_vertices (R : IntegerCube d) (c : Vertex d) :
    IsTranslate c ↑R.vertices ↑(R.shift c).vertices := by
  intro v
  simp only [Finset.mem_coe, IntegerCube.mem_vertices]
  refine forall_congr' fun i => ?_
  change R.corner i + c i ≤ v i + c i ∧ v i + c i < R.corner i + c i + (R.size : ℤ) ↔ _
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega

theorem IntegerCube.isTranslate_shift_lowerFace (R : IntegerCube d) (c : Vertex d) (i : Fin d) :
    IsTranslate c ↑(R.lowerFace i) ↑((R.shift c).lowerFace i) := by
  intro v
  simp only [Finset.mem_coe, IntegerCube.mem_lowerFace]
  rw [← Finset.mem_coe, ← Finset.mem_coe (s := R.vertices), R.isTranslate_shift_vertices c v]
  change _ ∧ v i + c i = R.corner i + c i ↔ _
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

theorem IntegerCube.isTranslate_shift_upperFace (R : IntegerCube d) (c : Vertex d) (i : Fin d) :
    IsTranslate c ↑(R.upperFace i) ↑((R.shift c).upperFace i) := by
  intro v
  simp only [Finset.mem_coe, IntegerCube.mem_upperFace]
  rw [← Finset.mem_coe, ← Finset.mem_coe (s := R.vertices), R.isTranslate_shift_vertices c v]
  change _ ∧ v i + c i + 1 = R.corner i + c i + (R.size : ℤ) ↔ _
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

theorem IntegerCube.shift_neg_shift (R : IntegerCube d) (c : Vertex d) :
    (R.shift (-c)).shift c = R := by
  simp only [IntegerCube.shift, neg_add_cancel_right]

/-- The centre of a shifted triadic cube. -/
theorem TriadicCube.center_shift' {Q : TriadicCube d} {c : Vertex d} (hc : ∀ i, Q.side ∣ c i)
    (i : Fin d) : (Q.shift c).center i = Q.center i + c i := by
  change Q.side * (Q.index i + c i / Q.side) = Q.side * Q.index i + c i
  rw [mul_add, Int.mul_ediv_cancel' (hc i)]

theorem TriadicCube.isTranslate_shift_vertices {Q : TriadicCube d} {c : Vertex d}
    (hc : ∀ i, Q.side ∣ c i) : IsTranslate c Q.vertices (Q.shift c).vertices :=
  TriadicCube.add_mem_shift_iff hc

theorem TriadicCube.toIntegerCube_shift {Q : TriadicCube d} {c : Vertex d}
    (hc : ∀ i, Q.side ∣ c i) : (Q.shift c).toIntegerCube = Q.toIntegerCube.shift c := by
  have h := TriadicCube.center_shift' hc
  change IntegerCube.mk _ _ = IntegerCube.mk _ _
  congr 1
  funext i
  have hi := h i
  change (Q.shift c).side * (Q.shift c).index i - (Q.shift c).side / 2 =
    Q.side * Q.index i - Q.side / 2 + c i
  change (Q.shift c).side * (Q.shift c).index i = Q.side * Q.index i + c i at hi
  rw [hi, TriadicCube.side_shift]
  ring

theorem TriadicCube.threeQuarterCube_shift {Q : TriadicCube d} {c : Vertex d}
    (hc : ∀ i, Q.side ∣ c i) : (Q.shift c).threeQuarterCube = Q.threeQuarterCube.shift c := by
  have h := TriadicCube.center_shift' hc
  change IntegerCube.mk _ _ = IntegerCube.mk _ _
  congr 1
  funext i
  change (Q.shift c).center i - _ = Q.center i - _ + c i
  rw [h i, TriadicCube.scale_shift]
  ring

/-- Test cubes move with shifts. -/
theorem TriadicCube.shift_mem_testCubes_iff {Q : TriadicCube d} {c : Vertex d}
    (hc : ∀ i, Q.side ∣ c i) (R : IntegerCube d) :
    R.shift c ∈ (Q.shift c).testCubes (Q.shift c).threeQuarterCube.vertices ↔
      R ∈ Q.testCubes Q.threeQuarterCube.vertices := by
  unfold TriadicCube.testCubes
  simp only [Set.mem_setOf_eq, TriadicCube.side_shift]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  rw [threeQuarterCube_shift hc]
  constructor
  · rintro ⟨x, hxR, hxT⟩
    refine ⟨x - c, ?_, ?_⟩
    · have := ((R.isTranslate_shift_vertices c).sub_mem_iff x).2 hxR
      exact this
    · exact ((Q.threeQuarterCube.isTranslate_shift_vertices c).sub_mem_iff x).2 hxT
  · rintro ⟨x, hxR, hxT⟩
    exact ⟨x + c, (R.isTranslate_shift_vertices c x).2 hxR,
      (Q.threeQuarterCube.isTranslate_shift_vertices c x).2 hxT⟩

/-- Large paths move with shifts. -/
theorem TriadicCube.largePath_shift_iff (Q : TriadicCube d) (c : Vertex d) (n : ℕ)
    (γ : Fin (n + 1) → Vertex d) :
    (Q.shift c).largePath n (fun j => γ j + c) ↔ Q.largePath n γ := by
  unfold TriadicCube.largePath
  simp only [TriadicCube.side_shift, Pi.add_apply, add_sub_add_right_eq_sub]

/-- Well-connected roots move with a translation of the configuration. -/
theorem TriadicCube.isWellConnectedRoot_shift_iff {Q : TriadicCube d} {c : Vertex d}
    (hc : ∀ i, Q.side ∣ c i) (ω : Configuration d) (r : Vertex d) :
    (Q.shift c).IsWellConnectedRoot (configurationTranslation c ω) (r + c) ↔
      Q.IsWellConnectedRoot ω r := by
  have hQ := TriadicCube.isTranslate_shift_vertices hc
  have hfl : ∀ i, IsTranslate c ↑(Q.toIntegerCube.lowerFace i)
      ↑((Q.shift c).toIntegerCube.lowerFace i) := fun i => by
    rw [toIntegerCube_shift hc]; exact Q.toIntegerCube.isTranslate_shift_lowerFace c i
  have hfu : ∀ i, IsTranslate c ↑(Q.toIntegerCube.upperFace i)
      ↑((Q.shift c).toIntegerCube.upperFace i) := fun i => by
    rw [toIntegerCube_shift hc]; exact Q.toIntegerCube.isTranslate_shift_upperFace c i
  unfold TriadicCube.IsWellConnectedRoot
  rw [isCrossingRoot_translation_iff c ω hQ hfl hfu r]
  refine and_congr Iff.rfl ?_
  have key : ∀ R : IntegerCube d,
      (CrossableRegion (configurationTranslation c ω) ↑(R.shift c).vertices
          (fun i => ↑((R.shift c).lowerFace i)) (fun i => ↑((R.shift c).upperFace i)) ∧
        ConnectsSelectedPaths (configurationTranslation c ω) ↑(R.shift c).vertices
          (Q.shift c).vertices (r + c) (Q.shift c).largePath) ↔
      (CrossableRegion ω ↑R.vertices (fun i => ↑(R.lowerFace i)) (fun i => ↑(R.upperFace i)) ∧
        ConnectsSelectedPaths ω ↑R.vertices Q.vertices r Q.largePath) := fun R =>
    and_congr (crossableRegion_translation_iff c ω (R.isTranslate_shift_vertices c)
        (R.isTranslate_shift_lowerFace c) (R.isTranslate_shift_upperFace c))
      (connectsSelectedPaths_translation_iff c ω (R.isTranslate_shift_vertices c) hQ
        (Q.largePath_shift_iff c) r)
  constructor
  · intro h R hR
    exact (key R).1 (h _ ((shift_mem_testCubes_iff hc R).2 hR))
  · intro h R' hR'
    rw [← R'.shift_neg_shift c] at hR' ⊢
    exact (key _).2 (h _ ((shift_mem_testCubes_iff hc _).1 hR'))

/-- Well-connectedness moves with a translation of the configuration. -/
theorem TriadicCube.shift_wellConnectedIn_translation_iff {Q : TriadicCube d} {c : Vertex d}
    (hc : ∀ i, Q.side ∣ c i) (ω : Configuration d) :
    (Q.shift c).wellConnectedIn (Q.shift c).threeQuarterCube.vertices
        (configurationTranslation c ω) ↔ Q.wellConnectedIn Q.threeQuarterCube.vertices ω := by
  rw [wellConnectedIn_threeQuarter_iff, wellConnectedIn_threeQuarter_iff]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r - c, (isWellConnectedRoot_shift_iff hc ω _).1 ?_⟩
    rwa [sub_add_cancel]
  · rintro ⟨r, hr⟩
    exact ⟨r + c, (isWellConnectedRoot_shift_iff hc ω r).2 hr⟩

/-- Well-connected cubes move with a translation of the configuration. -/
theorem TriadicCube.shift_mem_wellConnectedCubes_translation_iff {Q : TriadicCube d}
    {c : Vertex d} (hc : ∀ i, Q.side ∣ c i) (ω : Configuration d) :
    Q.shift c ∈ wellConnectedCubes (configurationTranslation c ω) ↔
      Q ∈ wellConnectedCubes ω := by
  unfold wellConnectedCubes
  simp only [Set.mem_setOf_eq, scale_shift]
  exact and_congr Iff.rfl (shift_wellConnectedIn_translation_iff hc ω)

/-- Good cubes move with a translation of the configuration. -/
theorem TriadicCube.shift_mem_goodCubes_translation_iff {Q : TriadicCube d} {c : Vertex d}
    (hc : ∀ i, Q.side ∣ c i) (ω : Configuration d) :
    Q.shift c ∈ goodCubes (configurationTranslation c ω) ↔ Q ∈ goodCubes ω := by
  unfold goodCubes goodOfWellConnected
  simp only [Set.mem_setOf_eq, scale_shift]
  constructor
  · rintro ⟨hpos, hm, hch⟩
    refine ⟨hpos, (shift_mem_wellConnectedCubes_translation_iff hc ω).1 hm, fun digits => ?_⟩
    have hcd : ∀ i, (Q.child digits).side ∣ c i := fun i =>
      (Dvd.intro_left 3 (Q.three_mul_side_child digits hpos)).trans (hc i)
    have h := hch digits
    rw [child_shift hpos hc] at h
    exact (shift_mem_wellConnectedCubes_translation_iff hcd ω).1 h
  · rintro ⟨hpos, hm, hch⟩
    refine ⟨hpos, (shift_mem_wellConnectedCubes_translation_iff hc ω).2 hm, fun digits => ?_⟩
    have hcd : ∀ i, (Q.child digits).side ∣ c i := fun i =>
      (Dvd.intro_left 3 (Q.three_mul_side_child digits hpos)).trans (hc i)
    rw [child_shift hpos hc]
    exact (shift_mem_wellConnectedCubes_translation_iff hcd ω).2 (hch digits)

/-- **Translation of the capped partition.** For `c ∈ 3ⁿ ℤᵈ`, the partition into good cubes
capped at scale `n` of the translated configuration is the translated partition. -/
theorem cappedCube_goodCubes_translation {n : ℕ} {c : Vertex d}
    (hc : ∀ i, (3 : ℤ) ^ n ∣ c i) (ω : Configuration d) (x : Vertex d) :
    TriadicCube.cappedCube (TriadicCube.goodCubes (configurationTranslation c ω)) n (x + c) =
      (TriadicCube.cappedCube (TriadicCube.goodCubes ω) n x).shift c :=
  TriadicCube.cappedCube_add hc (fun _ hR => TriadicCube.shift_mem_goodCubes_translation_iff
    (TriadicCube.side_dvd_of_scale_le hc hR.le) ω) x

/-- Crossing clusters move with a translation of the configuration. -/
theorem TriadicCube.add_mem_crossingCluster_shift_iff {Q : TriadicCube d} {c : Vertex d}
    (hc : ∀ i, Q.side ∣ c i) (ω : Configuration d) (y : Vertex d) :
    y + c ∈ (Q.shift c).crossingCluster (configurationTranslation c ω) ↔
      y ∈ Q.crossingCluster ω := by
  have hQ := TriadicCube.isTranslate_shift_vertices hc
  have hfl : ∀ i, IsTranslate c ↑(Q.toIntegerCube.lowerFace i)
      ↑((Q.shift c).toIntegerCube.lowerFace i) := fun i => by
    rw [toIntegerCube_shift hc]; exact Q.toIntegerCube.isTranslate_shift_lowerFace c i
  have hfu : ∀ i, IsTranslate c ↑(Q.toIntegerCube.upperFace i)
      ↑((Q.shift c).toIntegerCube.upperFace i) := fun i => by
    rw [toIntegerCube_shift hc]; exact Q.toIntegerCube.isTranslate_shift_upperFace c i
  constructor
  · rintro ⟨r, hr, hry⟩
    refine ⟨r - c, (isCrossingRoot_translation_iff c ω hQ hfl hfu _).1 ?_, ?_⟩
    · rwa [sub_add_cancel]
    · rwa [openIn_reachable_translation_sub_iff c ω hQ, add_sub_cancel_right] at hry
  · rintro ⟨r, hr, hry⟩
    exact ⟨r + c, (isCrossingRoot_translation_iff c ω hQ hfl hfu r).2 hr,
      (openIn_reachable_translation_iff c ω hQ r y).2 hry⟩

/-- Lexicographic order is invariant under translation. -/
theorem toLex_add_strictMono (c : Vertex d) :
    StrictMono fun b : Lex (Fin d → ℤ) => toLex (ofLex b + c) := by
  rintro a b ⟨i, hi, hlt⟩
  refine ⟨i, fun j hj => ?_, ?_⟩
  · change a j + c j = b j + c j
    rw [hi j hj]
  · change a i + c i < b i + c i
    have h : a i < b i := hlt
    omega

/-- The anchor order is invariant under translation. -/
theorem TriadicCube.anchorKey_shift_le_iff {Q : TriadicCube d} {c : Vertex d}
    (hc : ∀ i, Q.side ∣ c i) (y z : Vertex d) :
    (Q.shift c).anchorKey (y + c) ≤ (Q.shift c).anchorKey (z + c) ↔
      Q.anchorKey y ≤ Q.anchorKey z := by
  let φ : ℕ ×ₗ Lex (Fin d → ℤ) → ℕ ×ₗ Lex (Fin d → ℤ) := fun p =>
    toLex ((ofLex p).1, toLex (ofLex (ofLex p).2 + c))
  have hφ : StrictMono φ := by
    intro p q hpq
    rcases Prod.Lex.lt_iff.1 hpq with h | ⟨h1, h2⟩
    · exact Prod.Lex.lt_iff.2 (Or.inl h)
    · exact Prod.Lex.lt_iff.2 (Or.inr ⟨h1, toLex_add_strictMono c h2⟩)
  have hkey : ∀ w, (Q.shift c).anchorKey (w + c) = φ (Q.anchorKey w) := by
    intro w
    simp only [TriadicCube.anchorKey, φ, ofLex_toLex, center_shift' hc, Pi.add_apply,
      add_sub_add_right_eq_sub]
  rw [hkey, hkey]
  exact hφ.le_iff_le

/-- Anchors move with a translation of the configuration. -/
theorem TriadicCube.anchor_shift {Q : TriadicCube d} {c : Vertex d} (hc : ∀ i, Q.side ∣ c i)
    (ω : Configuration d) :
    (Q.shift c).anchor (configurationTranslation c ω) = Q.anchor ω + c := by
  have hmem := add_mem_crossingCluster_shift_iff hc ω
  have hiso : ∀ y, (Q.shift c).IsAnchor (configurationTranslation c ω) (y + c) ↔
      Q.IsAnchor ω y := by
    intro y
    unfold TriadicCube.IsAnchor
    rw [hmem]
    refine and_congr Iff.rfl ⟨fun h z hz => ?_, fun h z' hz' => ?_⟩
    · exact (anchorKey_shift_le_iff hc y z).1 (h _ ((hmem z).2 hz))
    · have hz : z' - c ∈ Q.crossingCluster ω := by rwa [← hmem, sub_add_cancel]
      have h' := (anchorKey_shift_le_iff hc y (z' - c)).2 (h _ hz)
      rwa [sub_add_cancel] at h'
  by_cases hne : (Q.crossingCluster ω).Nonempty
  · have hne' : ((Q.shift c).crossingCluster (configurationTranslation c ω)).Nonempty := by
      obtain ⟨y, hy⟩ := hne
      exact ⟨y + c, (hmem y).2 hy⟩
    rw [anchor_eq_iff hne', hiso]
    exact isAnchor_anchor hne
  · have h0 : Q.crossingCluster ω = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
    have h0' : (Q.shift c).crossingCluster (configurationTranslation c ω) = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hy
      have := (hmem (y - c)).1 (by rwa [sub_add_cancel])
      rw [h0] at this
      exact this
    rw [anchor_of_crossingCluster_eq_empty h0, anchor_of_crossingCluster_eq_empty h0']
    funext i
    exact center_shift' hc i

end Rigidity.Percolation
