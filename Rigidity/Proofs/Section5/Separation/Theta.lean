import Rigidity.Proofs.Section5.Separation.Sphere

/-!
# Lemma 5.19: the theta graph

The planar fact behind the case analysis of L2068-2089 (corrected draft): of three arcs with
common endpoints and disjoint interiors, one lies inside the Jordan curve formed by the other
two, as seen from a point `w` off the three arcs (`false_of_theta`).

The arcs `K₁, K₂, K₃` are unions of unit lattice segments. Suppose that the interior `Aᵢ` of
each arc lies outside the Jordan curve `Jᵢ` formed by the two others, and that `w` lies outside
the three curves. Let `W` be the component of `w` in the complement of `Θ = K₁ ∪ K₂ ∪ K₃`.
The insides `Iᵢ` are components of `ℝ² \ Θ`, pairwise distinct (`Iⱼ` has `Aₖ ⊆ Jⱼ` in its
closure, `Iₖ` does not) and distinct from `W`. A point of `Θ` which is not a lattice point lies
on an arc `Kᵢ`, hence in the closure of the two insides `Iⱼ`, `Iₖ`; off `Θ`, a small ball around
it consists of two half-balls, each contained in any component of `ℝ² \ Θ` it meets, so it is not
in the closure of `W` (pigeonhole). Hence `W` is closed in the plane minus the lattice points,
which is connected: `W` contains every non-lattice point, including those of `Θ`.
-/

open Set Topology

namespace Rigidity.Proofs.Section5

/-- Three pairwise disjoint sets cannot each contain one of two nonempty sets. -/
theorem false_of_three_disjoint {X Y Z H₁ H₂ : Set Plane} (hXY : Disjoint X Y)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (h₁ : H₁.Nonempty) (h₂ : H₂.Nonempty)
    (hX : H₁ ⊆ X ∨ H₂ ⊆ X) (hY : H₁ ⊆ Y ∨ H₂ ⊆ Y) (hZ : H₁ ⊆ Z ∨ H₂ ⊆ Z) : False := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  rcases hX with hX | hX <;> rcases hY with hY | hY <;> rcases hZ with hZ | hZ
  · exact hXY.ne_of_mem (hX ha) (hY ha) rfl
  · exact hXY.ne_of_mem (hX ha) (hY ha) rfl
  · exact hXZ.ne_of_mem (hX ha) (hZ ha) rfl
  · exact hYZ.ne_of_mem (hY hb) (hZ hb) rfl
  · exact hYZ.ne_of_mem (hY ha) (hZ ha) rfl
  · exact hXZ.ne_of_mem (hX hb) (hZ hb) rfl
  · exact hXY.ne_of_mem (hX hb) (hY hb) rfl
  · exact hXY.ne_of_mem (hX hb) (hY hb) rfl

/-- The inside of the curve formed by two arcs misses the third arc when its interior lies
outside. -/
theorem JordanSides.disjoint_arc {J I O K A : Set Plane} (h : JordanSides J I O) (hK : K ⊆ A ∪ J)
    (hA : A ⊆ O) : Disjoint I (K ∪ J) := by
  have hIJ : Disjoint I J := by
    rw [Set.disjoint_right]
    intro x hx hxI
    have : x ∈ I ∪ O := Or.inl hxI
    rw [h.union_eq] at this
    exact this hx
  refine Set.disjoint_union_right.2 ⟨?_, hIJ⟩
  rw [Set.disjoint_right]
  intro x hx hxI
  rcases hK hx with hxA | hxJ
  · exact h.disjoint.ne_of_mem hxI (hA hxA) rfl
  · exact hIJ.ne_of_mem hxI hxJ rfl

/-- A preconnected set off `J` meeting the inside lies in it. -/
theorem JordanSides.subset_inside {J I O H : Set Plane} (h : JordanSides J I O)
    (hH : IsPreconnected H) (hHJ : Disjoint H J) (hne : (H ∩ I).Nonempty) : H ⊆ I := by
  refine hH.subset_left_of_subset_union h.isOpen_inside h.isOpen_outside h.disjoint ?_ hne
  rw [h.union_eq]
  exact fun x hx hxJ => hHJ.ne_of_mem hx hxJ rfl

/-- Two insides are disjoint when a point outside the second lies on the first curve. -/
theorem JordanSides.disjoint_insides {J I O J' I' O' : Set Plane} {y : Plane}
    (h : JordanSides J I O) (h' : JordanSides J' I' O') (hIJ' : Disjoint I J') (hyJ : y ∈ J)
    (hyO' : y ∈ O') : Disjoint I I' := by
  refine Set.disjoint_left.2 fun x hxI hxI' => ?_
  have hsub : I ⊆ I' := h'.subset_inside h.isPreconnected_inside hIJ' ⟨x, hxI, hxI'⟩
  have hy : y ∈ closure I' := closure_mono hsub (h.subset_closure hyJ)
  exact (h'.disjoint.symm.closure_right h'.isOpen_outside).ne_of_mem hyO' hy rfl

/-- **Theta graph.** Three unions of lattice segments `K₁, K₂, K₃`, with interiors `Aᵢ` off the
other two, cannot all have their interior outside the Jordan curve formed by the other two, as
seen from a point `w` outside the three curves. -/
theorem false_of_theta {K₁ K₂ K₃ I₁ I₂ I₃ O₁ O₂ O₃ A₁ A₂ A₃ : Set Plane} {w : Plane}
    (hΘ : IsClosed (K₁ ∪ K₂ ∪ K₃))
    (hloc : ∀ v ∈ K₁ ∪ K₂ ∪ K₃, v ∉ range latticePoint → ∃ δ > 0, ∃ H₁ H₂ : Set Plane,
      IsPreconnected H₁ ∧ IsPreconnected H₂ ∧ H₁.Nonempty ∧ H₂.Nonempty ∧
      Disjoint H₁ (K₁ ∪ K₂ ∪ K₃) ∧ Disjoint H₂ (K₁ ∪ K₂ ∪ K₃) ∧
      Metric.ball v δ ⊆ H₁ ∪ H₂ ∪ (K₁ ∪ K₂ ∪ K₃))
    (h₁ : JordanSides (K₂ ∪ K₃) I₁ O₁) (h₂ : JordanSides (K₁ ∪ K₃) I₂ O₂)
    (h₃ : JordanSides (K₁ ∪ K₂) I₃ O₃)
    (hK₁ : K₁ ⊆ A₁ ∪ (K₂ ∪ K₃)) (hA₁O : A₁ ⊆ O₁)
    (hA₂ : A₂ ⊆ K₂) (hK₂ : K₂ ⊆ A₂ ∪ (K₁ ∪ K₃)) (hA₂O : A₂ ⊆ O₂) (hA₂n : A₂.Nonempty)
    (hA₃ : A₃ ⊆ K₃) (hK₃ : K₃ ⊆ A₃ ∪ (K₁ ∪ K₂)) (hA₃O : A₃ ⊆ O₃) (hA₃n : A₃.Nonempty)
    (hw : w ∉ K₁ ∪ K₂ ∪ K₃) (hw₁ : w ∈ O₁) (hw₂ : w ∈ O₂) (hw₃ : w ∈ O₃)
    (hy : ∃ y ∈ K₁ ∪ K₂ ∪ K₃, y ∉ range latticePoint) : False := by
  set Θ := K₁ ∪ K₂ ∪ K₃ with hΘdef
  -- the insides miss `Θ`
  have hI₁ : Disjoint I₁ Θ := by
    have := h₁.disjoint_arc hK₁ hA₁O
    rwa [show K₁ ∪ (K₂ ∪ K₃) = Θ by rw [hΘdef, union_assoc]] at this
  have hI₂ : Disjoint I₂ Θ := by
    have := h₂.disjoint_arc hK₂ hA₂O
    rwa [show K₂ ∪ (K₁ ∪ K₃) = Θ by rw [hΘdef]; ac_rfl] at this
  have hI₃ : Disjoint I₃ Θ := by
    have := h₃.disjoint_arc hK₃ hA₃O
    rwa [show K₃ ∪ (K₁ ∪ K₂) = Θ by rw [hΘdef]; ac_rfl] at this
  have hJ₁ : K₂ ∪ K₃ ⊆ Θ := by rw [hΘdef, union_assoc]; exact subset_union_right
  have hJ₂ : K₁ ∪ K₃ ⊆ Θ := union_subset (subset_union_left.trans subset_union_left)
    subset_union_right
  have hJ₃ : K₁ ∪ K₂ ⊆ Θ := subset_union_left
  -- the insides are pairwise disjoint
  obtain ⟨a₂, ha₂⟩ := hA₂n
  obtain ⟨a₃, ha₃⟩ := hA₃n
  have hI₁₂ : Disjoint I₁ I₂ := h₁.disjoint_insides h₂ (hI₁.mono_right hJ₂)
    (Or.inl (hA₂ ha₂)) (hA₂O ha₂)
  have hI₁₃ : Disjoint I₁ I₃ := h₁.disjoint_insides h₃ (hI₁.mono_right hJ₃)
    (Or.inr (hA₃ ha₃)) (hA₃O ha₃)
  have hI₂₃ : Disjoint I₂ I₃ := h₂.disjoint_insides h₃ (hI₂.mono_right hJ₃)
    (Or.inr (hA₃ ha₃)) (hA₃O ha₃)
  -- the component `W` of `w`
  set W := connectedComponentIn Θᶜ w with hWdef
  have hWo : IsOpen W := hΘ.isOpen_compl.connectedComponentIn
  have hWΘ : Disjoint W Θ :=
    Set.disjoint_left.2 fun x hx hxΘ => connectedComponentIn_subset _ _ hx hxΘ
  have hwW : w ∈ W := mem_connectedComponentIn hw
  have hWI : ∀ {J I O : Set Plane}, JordanSides J I O → J ⊆ Θ → w ∈ O → Disjoint W I := by
    intro J I O h hJ hwO
    have : W ⊆ O := by
      refine isPreconnected_connectedComponentIn.subset_left_of_subset_union h.isOpen_outside
        h.isOpen_inside h.disjoint.symm ?_ ⟨w, hwW, hwO⟩
      rw [union_comm, h.union_eq]
      exact fun x hx hxJ => hWΘ.ne_of_mem hx (hJ hxJ) rfl
    exact h.disjoint.symm.mono_left this
  have hW₁ := hWI h₁ hJ₁ hw₁
  have hW₂ := hWI h₂ hJ₂ hw₂
  have hW₃ := hWI h₃ hJ₃ hw₃
  -- absorption of the half-balls
  have habsW : ∀ H : Set Plane, IsPreconnected H → Disjoint H Θ → (H ∩ W).Nonempty → H ⊆ W := by
    rintro H hH hHΘ ⟨x, hxH, hxW⟩
    rw [hWdef, connectedComponentIn_eq (F := Θᶜ) (x := w) hxW]
    exact hH.subset_connectedComponentIn hxH fun z hz hzΘ => hHΘ.ne_of_mem hz hzΘ rfl
  have habsI : ∀ {J I O : Set Plane}, JordanSides J I O → J ⊆ Θ → ∀ H : Set Plane,
      IsPreconnected H → Disjoint H Θ → (H ∩ I).Nonempty → H ⊆ I :=
    fun h hJ H hH hHΘ hne => h.subset_inside hH (hHΘ.mono_right hJ) hne
  -- the closure of `W` misses the non-lattice points of `Θ`
  have hcl : closure W ∩ (range latticePoint)ᶜ ⊆ W := by
    rintro v ⟨hvW, hvl⟩
    by_cases hvΘ : v ∈ Θ
    · exfalso
      obtain ⟨δ, hδ, H₁, H₂, hH₁, hH₂, hn₁, hn₂, hd₁, hd₂, hball⟩ := hloc v hvΘ hvl
      have hpick : ∀ X : Set Plane, v ∈ closure X → Disjoint X Θ →
          (∀ H : Set Plane, IsPreconnected H → Disjoint H Θ → (H ∩ X).Nonempty → H ⊆ X) →
          H₁ ⊆ X ∨ H₂ ⊆ X := by
        intro X hvX hXΘ habs
        obtain ⟨x, hxX, hxb⟩ := Metric.mem_closure_iff.1 hvX δ hδ
        have hxb' : x ∈ Metric.ball v δ := by rw [Metric.mem_ball, dist_comm]; exact hxb
        rcases hball hxb' with (hx₁ | hx₂) | hxΘ
        · exact Or.inl (habs H₁ hH₁ hd₁ ⟨x, hx₁, hxX⟩)
        · exact Or.inr (habs H₂ hH₂ hd₂ ⟨x, hx₂, hxX⟩)
        · exact absurd hxΘ (hXΘ.ne_of_mem hxX · rfl)
      have hW := hpick W hvW hWΘ habsW
      rcases hvΘ with (hv₁ | hv₂) | hv₃
      · exact false_of_three_disjoint hW₂ hW₃ hI₂₃ hn₁ hn₂ hW
          (hpick I₂ (h₂.subset_closure (Or.inl hv₁)) hI₂ (habsI h₂ hJ₂))
          (hpick I₃ (h₃.subset_closure (Or.inl hv₁)) hI₃ (habsI h₃ hJ₃))
      · exact false_of_three_disjoint hW₁ hW₃ hI₁₃ hn₁ hn₂ hW
          (hpick I₁ (h₁.subset_closure (Or.inl hv₂)) hI₁ (habsI h₁ hJ₁))
          (hpick I₃ (h₃.subset_closure (Or.inr hv₂)) hI₃ (habsI h₃ hJ₃))
      · exact false_of_three_disjoint hW₁ hW₂ hI₁₂ hn₁ hn₂ hW
          (hpick I₁ (h₁.subset_closure (Or.inr hv₃)) hI₁ (habsI h₁ hJ₁))
          (hpick I₂ (h₂.subset_closure (Or.inr hv₃)) hI₂ (habsI h₂ hJ₂))
    · obtain ⟨x, hxV, hxW⟩ := mem_closure_iff.1 hvW _
        (hΘ.isOpen_compl.connectedComponentIn (x := v)) (mem_connectedComponentIn hvΘ)
      rw [hWdef, connectedComponentIn_eq (F := Θᶜ) (x := w) hxW, ← connectedComponentIn_eq hxV]
      exact mem_connectedComponentIn hvΘ
  -- hence `W` contains every non-lattice point
  have hS := isConnected_compl_range_latticePoint.isPreconnected
  have hSW : ((range latticePoint)ᶜ ∩ W).Nonempty := by
    rw [inter_comm]
    exact dense_compl_range_latticePoint.inter_open_nonempty W hWo ⟨w, hwW⟩
  have hsub := hS.subset_of_closure_inter_subset hWo hSW hcl
  obtain ⟨y, hyΘ, hyl⟩ := hy
  exact hWΘ.ne_of_mem (hsub hyl) hyΘ rfl

end Rigidity.Proofs.Section5
