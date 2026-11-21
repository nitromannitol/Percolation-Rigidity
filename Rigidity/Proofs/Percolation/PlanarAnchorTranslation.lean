import Rigidity.Proofs.Percolation.PlanarTranslation

/-!
# Translation of the anchors of meshed planar cubes

For a translation by `c`, where the side of `Q` divides `c`, the anchor property moves with the
translation of the configuration: inside the shifted cube and inside its square of side `9s`, a
translated vertex is joined to every translated long open walk exactly when the vertex is joined
to every long open walk before the translation. Since the anchor is chosen through its
displacement from the centre, the anchor of the shifted cube in the translated configuration is
the translated anchor.
-/

open LatticeProb.Percolation Rigidity.Proofs.Section5

namespace Rigidity.Percolation

/-- Translating a point moves it into the translated integer cube exactly when it was in the
cube. -/
theorem IntegerCube.add_mem_translate_vertices_iff (R : IntegerCube 2) (c v : Vertex 2) :
    v + c ∈ (R.translate c).vertices ↔ v ∈ R.vertices := by
  simp only [IntegerCube.mem_vertices, IntegerCube.corner_translate, IntegerCube.size_translate,
    Pi.add_apply]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega

/-- The square of side `9s` around a shifted cube is the translated square. -/
theorem TriadicCube.ninefold_shift {Q : TriadicCube 2} {c : Vertex 2} (hc : ∀ i, Q.side ∣ c i) :
    (Q.shift c).ninefold = Q.ninefold.translate c := by
  have hrad : (Q.shift c).ninefoldRadius = Q.ninefoldRadius := rfl
  simp only [TriadicCube.ninefold, IntegerCube.translate, IntegerCube.mk.injEq, scale_shift, hrad,
    and_true]
  funext i
  simp only [Pi.add_apply, center_shift hc]
  ring

theorem TriadicCube.add_mem_ninefold_shift_iff {Q : TriadicCube 2} {c : Vertex 2}
    (hc : ∀ i, Q.side ∣ c i) (v : Vertex 2) :
    v + c ∈ (↑(Q.shift c).ninefold.vertices : Set (Vertex 2)) ↔
      v ∈ (↑Q.ninefold.vertices : Set (Vertex 2)) := by
  rw [Finset.mem_coe, Finset.mem_coe, ninefold_shift hc]
  exact IntegerCube.add_mem_translate_vertices_iff _ c v

/-- Being joined inside a region to every long open walk moves with translations. -/
theorem forall_reachIn_long_translation_iff (c : Vertex 2) (ω : Configuration 2)
    {S S' : Set (Vertex 2)} (hS : ∀ v, v + c ∈ S' ↔ v ∈ S) (a : Vertex 2) (w : ℤ) :
    (∀ (x y : Vertex 2) (k : Fin 2), ReachIn (configurationTranslation c ω) S' x y →
        x k + w ≤ y k → ReachIn (configurationTranslation c ω) S' (a + c) x) ↔
      ∀ (x y : Vertex 2) (k : Fin 2), ReachIn ω S x y → x k + w ≤ y k → ReachIn ω S a x := by
  constructor
  · intro h x y k hxy hlong
    have := h (x + c) (y + c) k ((reachIn_translation_iff c ω hS x y).2 hxy)
      (by simp only [Pi.add_apply]; omega)
    exact (reachIn_translation_iff c ω hS a x).1 this
  · intro h x y k hxy hlong
    have hxy' : ReachIn ω S (x - c) (y - c) := by
      rw [← reachIn_translation_iff c ω hS, sub_add_cancel, sub_add_cancel]
      exact hxy
    have := h (x - c) (y - c) k hxy' (by simp only [Pi.sub_apply]; omega)
    rw [← reachIn_translation_iff c ω hS, sub_add_cancel] at this
    exact this

/-- The anchor property moves with translations. -/
theorem TriadicCube.isPlanarAnchor_shift_iff {Q : TriadicCube 2} {c : Vertex 2}
    (hc : ∀ i, Q.side ∣ c i) (ω : Configuration 2) (a : Vertex 2) :
    (Q.shift c).IsPlanarAnchor (configurationTranslation c ω) (a + c) ↔ Q.IsPlanarAnchor ω a :=
  and_congr (add_mem_shift_iff hc a)
    (and_congr (forall_reachIn_long_translation_iff c ω (add_mem_shift_iff hc) a _)
      (forall_reachIn_long_translation_iff c ω (add_mem_ninefold_shift_iff hc) a _))

/-- **Translation of anchors.** The anchor of the shifted cube in the translated configuration is
the translated anchor. -/
theorem TriadicCube.planarAnchor_shift {Q : TriadicCube 2} {c : Vertex 2}
    (hc : ∀ i, Q.side ∣ c i) (ω : Configuration 2) :
    (Q.shift c).planarAnchor (configurationTranslation c ω) = Q.planarAnchor ω + c := by
  have hcen : (Q.shift c).center = Q.center + c := funext fun i => center_shift hc i
  have hpred : (fun e => (Q.shift c).IsPlanarAnchor (configurationTranslation c ω)
      ((Q.shift c).center + e)) = fun e => Q.IsPlanarAnchor ω (Q.center + e) := by
    funext e
    rw [hcen, show Q.center + c + e = Q.center + e + c by abel]
    exact propext (isPlanarAnchor_shift_iff hc ω _)
  unfold planarAnchor
  by_cases h : Q.planarMeshed ω ∧ 1000 ≤ 3 ^ Q.scale
  · have h' : (Q.shift c).planarMeshed (configurationTranslation c ω) ∧
        1000 ≤ 3 ^ (Q.shift c).scale := ⟨(shift_planarMeshed_translation_iff hc ω).2 h.1, h.2⟩
    rw [if_pos h', if_pos h, hpred, hcen]
    abel
  · have h' : ¬ ((Q.shift c).planarMeshed (configurationTranslation c ω) ∧
        1000 ≤ 3 ^ (Q.shift c).scale) := fun h'' =>
      h ⟨(shift_planarMeshed_translation_iff hc ω).1 h''.1, h''.2⟩
    rw [if_neg h', if_neg h, hcen]

end Rigidity.Percolation
