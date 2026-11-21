import Rigidity.Proofs.Percolation.PlanarPartition
import Rigidity.Proofs.Percolation.TriadicCappedPartition
import LatticeProb.Prob.Percolation.OpenGraphTranslation
import LatticeProb.Prob.Percolation.LatticeBondTranslationLaw

/-!
# Translations of planar meshes, good cubes and capped partitions

Translating a configuration by `c` moves its open graph by `c`. Open connections inside regions,
strip meshes of integer squares and meshed triadic cubes move with it; for a vector `c` of `3ⁿ ℤ²`
so do the good cubes of scale at most `n` and the partition of `ℤ²` capped at scale `n`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.Proofs.Section5

namespace Rigidity.Percolation

/-- Open connections inside a region move with a translation of the configuration. -/
theorem reachIn_translation_iff (c : Vertex 2) (ω : Configuration 2) {S S' : Set (Vertex 2)}
    (hS : ∀ v, v + c ∈ S' ↔ v ∈ S) (x y : Vertex 2) :
    ReachIn (configurationTranslation c ω) S' (x + c) (y + c) ↔ ReachIn ω S x y := by
  constructor
  · rintro ⟨W, hW⟩
    let f := (openGraphTranslation c ω).symm.toHom
    refine ⟨(W.map f).copy (add_sub_cancel_right x c) (add_sub_cancel_right y c), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    have hv' := hW v hv
    change v - c ∈ S
    rw [← hS, sub_add_cancel]
    exact hv'
  · rintro ⟨W, hW⟩
    let f := (openGraphTranslation c ω).toHom
    refine ⟨(W.map f).copy rfl rfl, ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact (hS v).2 (hW v hv)

/-- The integer cube moved by `c`. -/
def IntegerCube.translate (R : IntegerCube 2) (c : Vertex 2) : IntegerCube 2 :=
  ⟨R.corner + c, R.size⟩

@[simp] theorem IntegerCube.size_translate (R : IntegerCube 2) (c : Vertex 2) :
    (R.translate c).size = R.size := rfl

@[simp] theorem IntegerCube.corner_translate (R : IntegerCube 2) (c : Vertex 2) (i : Fin 2) :
    (R.translate c).corner i = R.corner i + c i := rfl

theorem IntegerCube.translate_neg_translate (R : IntegerCube 2) (c : Vertex 2) :
    (R.translate (-c)).translate c = R := by
  simp only [translate, neg_add_cancel_right]

theorem IntegerCube.add_mem_hStrip_translate_iff (R : IntegerCube 2) (c : Vertex 2) (r : ℤ)
    (w : ℕ) (v : Vertex 2) :
    v + c ∈ (R.translate c).hStrip (r + c 1) w ↔ v ∈ R.hStrip r w := by
  simp only [hStrip, Set.mem_setOf_eq, corner_translate, size_translate, Pi.add_apply]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega

theorem IntegerCube.add_mem_vStrip_translate_iff (R : IntegerCube 2) (c : Vertex 2) (r : ℤ)
    (w : ℕ) (v : Vertex 2) :
    v + c ∈ (R.translate c).vStrip (r + c 0) w ↔ v ∈ R.vStrip r w := by
  simp only [vStrip, Set.mem_setOf_eq, corner_translate, size_translate, Pi.add_apply]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega

/-- Strip meshes move with a translation of the configuration. -/
theorem planarMesh_translation_iff (c : Vertex 2) (ω : Configuration 2) (R : IntegerCube 2)
    (w : ℕ) : PlanarMesh (configurationTranslation c ω) (R.translate c) w ↔ PlanarMesh ω R w := by
  have hh := fun r v => (R.add_mem_hStrip_translate_iff c r w v)
  have hv := fun r v => (R.add_mem_vStrip_translate_iff c r w v)
  unfold PlanarMesh
  simp only [IntegerCube.corner_translate, IntegerCube.size_translate]
  constructor
  · rintro ⟨hH, hV⟩
    refine ⟨fun r hr1 hr2 => ?_, fun r hr1 hr2 => ?_⟩
    · obtain ⟨a, b, hab, ha, hb⟩ := hH (r + c 1) (by omega) (by omega)
      refine ⟨a - c, b - c, ?_, by simp only [Pi.sub_apply]; omega,
        by simp only [Pi.sub_apply]; omega⟩
      rw [← reachIn_translation_iff c ω (hh r), sub_add_cancel, sub_add_cancel]
      exact hab
    · obtain ⟨a, b, hab, ha, hb⟩ := hV (r + c 0) (by omega) (by omega)
      refine ⟨a - c, b - c, ?_, by simp only [Pi.sub_apply]; omega,
        by simp only [Pi.sub_apply]; omega⟩
      rw [← reachIn_translation_iff c ω (hv r), sub_add_cancel, sub_add_cancel]
      exact hab
  · rintro ⟨hH, hV⟩
    refine ⟨fun r hr1 hr2 => ?_, fun r hr1 hr2 => ?_⟩
    · obtain ⟨a, b, hab, ha, hb⟩ := hH (r - c 1) (by omega) (by omega)
      have hr : r = r - c 1 + c 1 := by ring
      refine ⟨a + c, b + c, ?_, by simp only [Pi.add_apply]; omega,
        by simp only [Pi.add_apply]; omega⟩
      rw [hr, reachIn_translation_iff c ω (hh (r - c 1))]
      exact hab
    · obtain ⟨a, b, hab, ha, hb⟩ := hV (r - c 0) (by omega) (by omega)
      have hr : r = r - c 0 + c 0 := by ring
      refine ⟨a + c, b + c, ?_, by simp only [Pi.add_apply]; omega,
        by simp only [Pi.add_apply]; omega⟩
      rw [hr, reachIn_translation_iff c ω (hv (r - c 0))]
      exact hab

/-- The centre of a shifted cube. -/
theorem TriadicCube.center_shift {Q : TriadicCube 2} {c : Vertex 2} (hc : ∀ i, Q.side ∣ c i)
    (i : Fin 2) : (Q.shift c).center i = Q.center i + c i := by
  change Q.side * (Q.index i + c i / Q.side) = Q.side * Q.index i + c i
  rw [mul_add, Int.mul_ediv_cancel' (hc i)]

/-- The squares around a shifted cube are the translated squares. -/
theorem TriadicCube.translate_mem_planarSquares_shift_iff {Q : TriadicCube 2} {c : Vertex 2}
    (hc : ∀ i, Q.side ∣ c i) (R : IntegerCube 2) :
    R.translate c ∈ (Q.shift c).planarSquares ↔ R ∈ Q.planarSquares := by
  have hrad : (Q.shift c).ninefoldRadius = Q.ninefoldRadius := rfl
  simp only [mem_planarSquares, IntegerCube.size_translate, IntegerCube.corner_translate,
    scale_shift, center_shift hc, hrad]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun i => ?_))
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega

/-- Meshed cubes move with a translation of the configuration. -/
theorem TriadicCube.shift_planarMeshed_translation_iff {Q : TriadicCube 2} {c : Vertex 2}
    (hc : ∀ i, Q.side ∣ c i) (ω : Configuration 2) :
    (Q.shift c).planarMeshed (configurationTranslation c ω) ↔ Q.planarMeshed ω := by
  unfold planarMeshed
  simp only [scale_shift]
  constructor
  · intro h R hR
    exact (planarMesh_translation_iff c ω R _).1
      (h _ ((translate_mem_planarSquares_shift_iff hc R).2 hR))
  · intro h R' hR'
    rw [← R'.translate_neg_translate c] at hR' ⊢
    exact (planarMesh_translation_iff c ω _ _).2
      (h _ ((translate_mem_planarSquares_shift_iff hc _).1 hR'))

/-- Good planar cubes move with a translation of the configuration. -/
theorem TriadicCube.shift_mem_planarGoodCubes_translation_iff {Q : TriadicCube 2}
    {c : Vertex 2} (hc : ∀ i, Q.side ∣ c i) (ω : Configuration 2) :
    Q.shift c ∈ planarGoodCubes (configurationTranslation c ω) ↔ Q ∈ planarGoodCubes ω := by
  unfold planarGoodCubes goodOfWellConnected planarMeshedFamily
  simp only [Set.mem_setOf_eq, scale_shift]
  constructor
  · rintro ⟨hpos, ⟨h7, hm⟩, hch⟩
    refine ⟨hpos, ⟨h7, (shift_planarMeshed_translation_iff hc ω).1 hm⟩, fun digits => ?_⟩
    have hcd : ∀ i, (Q.child digits).side ∣ c i := fun i =>
      (Dvd.intro_left 3 (Q.three_mul_side_child digits hpos)).trans (hc i)
    obtain ⟨h7', hm'⟩ := hch digits
    rw [child_shift hpos hc] at h7' hm'
    exact ⟨h7', (shift_planarMeshed_translation_iff hcd ω).1 hm'⟩
  · rintro ⟨hpos, ⟨h7, hm⟩, hch⟩
    refine ⟨hpos, ⟨h7, (shift_planarMeshed_translation_iff hc ω).2 hm⟩, fun digits => ?_⟩
    have hcd : ∀ i, (Q.child digits).side ∣ c i := fun i =>
      (Dvd.intro_left 3 (Q.three_mul_side_child digits hpos)).trans (hc i)
    obtain ⟨h7', hm'⟩ := hch digits
    rw [child_shift hpos hc]
    exact ⟨h7', (shift_planarMeshed_translation_iff hcd ω).2 hm'⟩

/-- **Translation of the capped planar partition.** For `c ∈ 3ⁿ ℤ²`, the partition capped at
scale `n` of the translated configuration is the translated partition. -/
theorem cappedCube_planarGoodCubes_translation {n : ℕ} {c : Vertex 2}
    (hc : ∀ i, (3 : ℤ) ^ n ∣ c i) (ω : Configuration 2) (x : Vertex 2) :
    TriadicCube.cappedCube (planarGoodCubes (configurationTranslation c ω)) n (x + c) =
      (TriadicCube.cappedCube (planarGoodCubes ω) n x).shift c :=
  TriadicCube.cappedCube_add hc (fun _ hR => TriadicCube.shift_mem_planarGoodCubes_translation_iff
    (TriadicCube.side_dvd_of_scale_le hc hR.le) ω) x

end Rigidity.Percolation
