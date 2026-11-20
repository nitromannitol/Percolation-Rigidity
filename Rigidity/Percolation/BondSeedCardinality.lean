import Rigidity.Percolation.BondSeeds

/-!
# Size of bond seeds

The number of bonds internal to a finite vertex region is bounded in terms of
its vertex count. This gives a uniform seed-probability bound for families of
bounded-size regions.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- A finite vertex region has at most the square of its number of vertices
in internal bonds. -/
theorem card_localBonds_le_sq {d : ℕ} {U : Set (Vertex d)} (hU : U.Finite) :
    (finite_localBonds hU).toFinset.card ≤ hU.toFinset.card ^ 2 := by
  let f : Vertex d × Vertex d → Sym2 (Vertex d) := fun xy => s(xy.1, xy.2)
  have himage : Subtype.val '' localBonds U ⊆ f '' (U ×ˢ U) := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨x, y, hxy, _⟩ := e.property
    refine ⟨(x, y), ⟨?_, ?_⟩, hxy.symm⟩
    · exact he x (hxy ▸ Sym2.mem_mk_left x y)
    · exact he y (hxy ▸ Sym2.mem_mk_right x y)
  have hfinite : (f '' (U ×ˢ U)).Finite := (hU.prod hU).image f
  calc
    (finite_localBonds hU).toFinset.card = (localBonds U).ncard :=
      (Set.ncard_eq_toFinset_card _ _).symm
    _ = (Subtype.val '' localBonds U).ncard :=
      (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (f '' (U ×ˢ U)).ncard := Set.ncard_le_ncard himage hfinite
    _ ≤ (U ×ˢ U).ncard := Set.ncard_image_le (hU.prod hU)
    _ = hU.toFinset.card ^ 2 := by
      rw [Set.ncard_prod, Set.ncard_eq_toFinset_card U hU, pow_two]

/-- A bound on the number of vertices gives a uniform bound on the number of
internal bonds. -/
theorem card_localBonds_le_of_card_le {d : ℕ} {U : Set (Vertex d)} (hU : U.Finite)
    {M : ℕ} (hM : hU.toFinset.card ≤ M) :
    (finite_localBonds hU).toFinset.card ≤ M ^ 2 :=
  (card_localBonds_le_sq hU).trans (Nat.pow_le_pow_left hM _)

end Rigidity.Percolation
