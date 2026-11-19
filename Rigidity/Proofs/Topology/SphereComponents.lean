import Rigidity.Proofs.Topology.SphereChart

/-!
# Transport of planar components to the sphere

The bounded complementary component remains away from the projection pole; the unbounded
component joins the pole. Both components retain their common frontier.
-/

open Set Metric Bornology

namespace Rigidity.Topology

open Rigidity.External MatedCRTHarmonic.Planar.Jordan

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

/-- Two planar complementary components with a common frontier determine two sphere components. -/
theorem sphere_components_of_plane (p : S2) (J U V : Set Plane)
    (hUo : IsOpen U) (hVo : IsOpen V) (hUc : IsConnected U) (hVc : IsConnected V)
    (hUb : IsBounded U) (hVu : ¬ IsBounded V) (hUV : Disjoint U V)
    (hcover : U ∪ V = Jᶜ) (hUf : frontier U = J) (hVf : frontier V = J) :
    ∃ A B : Set S2, IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧ Disjoint A B ∧
      A ∪ B = ((stereographic' 2 p).symm '' J)ᶜ ∧
      frontier A = (stereographic' 2 p).symm '' J ∧
      frontier B = (stereographic' 2 p).symm '' J := by
  let e := stereographic' 2 p
  let i := e.symm
  let A : Set S2 := i '' U
  let C : Set S2 := i '' V
  let K : Set S2 := i '' J
  let B : Set S2 := C ∪ {p}
  have hi : Topology.IsOpenEmbedding i := stereographic_symm_openEmbedding p
  have hnonpole (z : Plane) : i z ≠ p := by
    have hs := e.map_target (show z ∈ e.target by simp [e])
    simpa only [e, i, stereographic'_source, mem_compl_iff, mem_singleton_iff] using hs
  have hrange : range i = ({p} : Set S2)ᶜ := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      simpa only [mem_compl_iff, mem_singleton_iff] using hnonpole w
    · intro hz
      have hz' : z ∈ e.source := by simpa only [e, stereographic'_source] using hz
      exact ⟨e z, e.left_inv hz'⟩
  have hpart : A ∪ C ∪ K = ({p} : Set S2)ᶜ := by
    change (i '' U ∪ i '' V) ∪ i '' J = _
    rw [← image_union, ← image_union, hcover, compl_union_self, image_univ, hrange]
  have hpA : p ∉ A := by
    rintro ⟨z, _, hz⟩
    exact hnonpole z hz
  have hpK : p ∉ K := by
    rintro ⟨z, _, hz⟩
    exact hnonpole z hz
  have hUK : Disjoint U J := by
    rw [← hUf]
    exact disjoint_frontier_iff_isOpen.mpr hUo |>.symm
  have hVK : Disjoint V J := by
    rw [← hVf]
    exact disjoint_frontier_iff_isOpen.mpr hVo |>.symm
  have hAC : Disjoint A C := (disjoint_image_iff hi.injective).mpr hUV
  have hAK : Disjoint A K := (disjoint_image_iff hi.injective).mpr hUK
  have hCK : Disjoint C K := (disjoint_image_iff hi.injective).mpr hVK
  have hAo : IsOpen A := hi.isOpenMap U hUo
  have hAf : frontier A = K := by
    change frontier (i '' U) = i '' J
    simpa only [hUf] using frontier_stereographic_symm_image p hUo hUb
  have hAclosure : closure A = A ∪ K := by rw [closure_eq_self_union_frontier, hAf]
  have hpart' (z : S2) : ((z ∈ A ∨ z ∈ C) ∨ z ∈ K) ↔ z ≠ p := by
    have h := Set.ext_iff.mp hpart z
    simpa only [mem_union, mem_compl_iff, mem_singleton_iff] using h
  have hB_eq : B = (closure A)ᶜ := by
    rw [hAclosure]
    ext z
    have hz := hpart' z
    have hac := disjoint_left.mp hAC
    have hak := disjoint_left.mp hAK
    have hck := disjoint_left.mp hCK
    simp only [B, mem_union, mem_singleton_iff, mem_compl_iff, not_or]
    constructor
    · rintro (hzC | rfl)
      · exact ⟨fun hzA => hac hzA hzC, fun hzK => hck hzC hzK⟩
      · exact ⟨hpA, hpK⟩
    · rintro ⟨hzA, hzK⟩
      by_cases hzp : z = p
      · exact Or.inr hzp
      · rcases hz.mpr hzp with (hzA' | hzC) | hzK'
        · exact (hzA hzA').elim
        · exact Or.inl hzC
        · exact (hzK hzK').elim
  have hBo : IsOpen B := hB_eq ▸ isClosed_closure.isOpen_compl
  have hBc : IsConnected B := by
    have hCc : IsConnected C := hVc.image i hi.continuous.continuousOn
    have hp : p ∈ closure C := pole_mem_closure_image_of_unbounded p hVu
    apply hCc.subset_closure (subset_union_left) ?_
    exact union_subset subset_closure (singleton_subset_iff.mpr hp)
  have hAB : Disjoint A B := by
    rw [hB_eq]
    exact disjoint_compl_right.mono_left subset_closure
  have hABcover : A ∪ B = Kᶜ := by
    rw [hB_eq, hAclosure]
    ext z
    have hak := disjoint_left.mp hAK
    simp only [mem_union, mem_compl_iff, not_or]
    constructor
    · rintro (hzA | ⟨_, hzK⟩)
      · exact fun hzK => hak hzA hzK
      · exact hzK
    · intro hzK
      by_cases hzA : z ∈ A
      · exact Or.inl hzA
      · exact Or.inr ⟨hzA, hzK⟩
  have hBf : frontier B = K := by
    apply Set.Subset.antisymm
    · rw [hB_eq, frontier_compl]
      exact frontier_closure_subset.trans_eq hAf
    · intro z hz
      have hzcl : z ∈ closure C := by
        have hz' : z ∈ i '' frontier V := by simpa only [hVf] using hz
        exact image_closure_subset_closure_image hi.continuous (image_mono frontier_subset_closure hz')
      have hzB : z ∉ B := by
        rintro (hzC | hzp)
        · exact (disjoint_left.mp hCK) hzC hz
        · exact hpK (by simpa only [mem_singleton_iff] using hzp ▸ hz)
      change z ∈ closure B ∧ z ∉ interior B
      exact ⟨closure_mono subset_union_left hzcl, fun hz' => hzB (interior_subset hz')⟩
  exact ⟨A, B, hAo, hBo, hUc.image i hi.continuous.continuousOn, hBc, hAB, hABcover, hAf, hBf⟩

end Rigidity.Topology
