import Rigidity.Proofs.Section5.KestenChannelCut

/-!
# Local connections of neighboring good blocks

Kesten channels in adjacent very-good blocks connect inside the union of the two blocks.
-/

open LatticeProb.Percolation Rigidity.Section5

namespace Rigidity.Proofs.Section5.Kesten

/-- A channel remains a channel in any set containing its cube. -/
theorem IsChannel.of_cube_subset {ω : Configuration 2} {T S : Set (Vertex 2)}
    {c y : Vertex 2} {r w j : ℕ} {i k : Fin 2}
    (h : IsChannel ω T c r w j i k y) (hS : cubeAt c r ⊆ S) :
    IsChannel ω S c r w j i k y := by
  obtain ⟨z, W, hW, hy, hz⟩ := h
  exact ⟨z, W, fun v hv => ⟨(hW v hv).1, hS (hW v hv).1.1⟩, hy, hz⟩

/-- Any two channels of a very-good block are connected inside the block. -/
theorem channels_reachable_in_cube {ω : Configuration 2} {R : ℕ} {c y y' : Vertex 2}
    {j j' : ℕ} (hR : 3210 ≤ R) (hc : IsVeryGood ω c (11 * R / 10))
    (hj : j < (2 * (11 * R / 10) + 1) / chanWidth (11 * R / 10))
    (hj' : j' < (2 * (11 * R / 10) + 1) / chanWidth (11 * R / 10))
    (hy : AnyChannel ω ∅ c (11 * R / 10) j y)
    (hy' : AnyChannel ω ∅ c (11 * R / 10) j' y') :
    ReachIn ω (cubeAt c (11 * R / 10)) y y' := by
  set r := 11 * R / 10
  have hp := params (Cf := 0) (R := R) (by omega)
  have hw : 1 ≤ chanWidth r := hp.2.1
  have hr : r = R + R / 10 := hp.1
  have hm : 2 * chanWidth r ≤ R / 10 := hp.2.2.1
  have hN : 0 < (2 * r + 1) / chanWidth r := Nat.div_pos (by omega) (by omega)
  let J := Finset.range ((2 * r + 1) / chanWidth r)
  have hJ : ∀ j ∈ J, j < (2 * r + 1) / chanWidth r := fun j hj => Finset.mem_range.1 hj
  have hcard : (∅ : Finset (Vertex 2)).card < J.card := by simpa [J] using hN
  obtain ⟨jH, hjH, yH, hH⟩ := exists_unhit_channel hc.2.1 ∅ J hJ hw hcard
  obtain ⟨jV, hjV, yV, hV⟩ := exists_unhit_channel hc.2.2 ∅ J hJ hw hcard
  have hcross {i l : ℕ} {u v : Vertex 2}
      (hu : IsChannel ω (↑(∅ : Finset (Vertex 2)))ᶜ c r (chanWidth r) i 0 1 u)
      (hv : IsChannel ω (↑(∅ : Finset (Vertex 2)))ᶜ c r (chanWidth r) l 1 0 v)
      (hi : i < (2 * r + 1) / chanWidth r) (hl : l < (2 * r + 1) / chanWidth r) :
      ReachIn ω (cubeAt c r) u v :=
    reachIn_same_cube (hu.of_cube_subset Set.Subset.rfl) (hv.of_cube_subset Set.Subset.rfl) hi hl
  rcases hy with hy | hy <;> rcases hy' with hy' | hy'
  · exact (hcross hy hV hj (hJ jV hjV)).trans (hcross hy' hV hj' (hJ jV hjV)).symm
  · exact hcross hy hy' hj hj'
  · exact (hcross hy' hy hj' hj).symm
  · exact (hcross hH hy (hJ jH hjH) hj).symm.trans (hcross hH hy' (hJ jH hjH) hj')

/-- Neighboring very-good blocks have channels joined inside their union. -/
theorem linked_of_neighbours_in_union {ω : Configuration 2} {R : ℕ}
    {a b : Vertex 2} (hR : 3210 ≤ R)
    (ha : IsVeryGood ω a (11 * R / 10)) (hb : IsVeryGood ω b (11 * R / 10))
    (hab : (b 0 = a 0 + (2 * R + 1) ∧ b 1 = a 1) ∨
      (b 1 = a 1 + (2 * R + 1) ∧ b 0 = a 0)) :
    ∃ j < (2 * (11 * R / 10) + 1) / chanWidth (11 * R / 10), ∃ y,
      AnyChannel ω ∅ a (11 * R / 10) j y ∧
      ∃ j' < (2 * (11 * R / 10) + 1) / chanWidth (11 * R / 10), ∃ y',
        AnyChannel ω ∅ b (11 * R / 10) j' y' ∧
        ReachIn ω (cubeAt a (11 * R / 10) ∪ cubeAt b (11 * R / 10)) y y' := by
  set r := 11 * R / 10
  have hp := params (Cf := 0) (R := R) (by omega)
  have hr : r = R + R / 10 := hp.1
  have hw : 1 ≤ chanWidth r := hp.2.1
  have hm : (0 + 2) * chanWidth r ≤ R / 10 := hp.2.2.1
  obtain ⟨j₀, _, hblock⟩ := exists_overlap_block (Cf := 0) hr hw hm
  let J := Finset.Ico j₀ (j₀ + 1)
  have hJ : ∀ j ∈ J, j < (2 * r + 1) / chanWidth r := fun j hj => (hblock j hj).1
  have hcardJ : (∅ : Finset (Vertex 2)).card < J.card := by simp [J]
  have hN : 0 < (2 * r + 1) / chanWidth r := by
    have := hJ j₀ (by simp [J])
    omega
  let K := Finset.range ((2 * r + 1) / chanWidth r)
  have hK : ∀ j ∈ K, j < (2 * r + 1) / chanWidth r := fun j hj => Finset.mem_range.1 hj
  have hcardK : (∅ : Finset (Vertex 2)).card < K.card := by simpa [K] using hN
  rcases hab with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · obtain ⟨jV, hjV, yV, hV⟩ := exists_unhit_channel ha.2.2 ∅ J hJ hw hcardJ
    obtain ⟨jH, hjH, yH, hH⟩ := exists_unhit_channel hb.2.1 ∅ K hK hw hcardK
    have hV1 := cast_succ_mul_le_of_lt_div (hJ jV hjV)
    have hH1 := cast_succ_mul_le_of_lt_div (hK jH hjH)
    have hH0 : (0 : ℤ) ≤ jH * chanWidth r := by positivity
    have hV2 : ((2 * R + 1 : ℕ) : ℤ) ≤ ((jV * chanWidth r : ℕ) : ℤ) := by
      exact_mod_cast (hblock jV hjV).2
    push_cast at hV2
    refine ⟨jV, hJ jV hjV, yV, Or.inr hV, jH, hK jH hjH, yH, Or.inl hH, ?_⟩
    exact (reachIn_of_channels (hH.of_cube_subset Set.subset_union_right)
      (hV.of_cube_subset Set.subset_union_left) (by linarith) (by linarith)
      (by linarith) (by linarith)).symm
  · obtain ⟨jH, hjH, yH, hH⟩ := exists_unhit_channel ha.2.1 ∅ J hJ hw hcardJ
    obtain ⟨jV, hjV, yV, hV⟩ := exists_unhit_channel hb.2.2 ∅ K hK hw hcardK
    have hH1 := cast_succ_mul_le_of_lt_div (hJ jH hjH)
    have hV1 := cast_succ_mul_le_of_lt_div (hK jV hjV)
    have hV0 : (0 : ℤ) ≤ jV * chanWidth r := by positivity
    have hH2 : ((2 * R + 1 : ℕ) : ℤ) ≤ ((jH * chanWidth r : ℕ) : ℤ) := by
      exact_mod_cast (hblock jH hjH).2
    push_cast at hH2
    refine ⟨jH, hJ jH hjH, yH, Or.inl hH, jV, hK jV hjV, yV, Or.inr hV, ?_⟩
    exact reachIn_of_channels (hH.of_cube_subset Set.subset_union_left)
      (hV.of_cube_subset Set.subset_union_right) (by linarith) (by linarith)
      (by linarith) (by linarith)

end Rigidity.Proofs.Section5.Kesten
