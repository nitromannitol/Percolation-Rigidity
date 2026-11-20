import Rigidity.Proofs.Section5.RenormalizedCrossingLift
import Rigidity.Proofs.Section5.PlanarFieldTranslation

/-!
# Isometries of open planar site graphs

Translations and coordinate swaps identify the site graphs of transformed fields with
subgraphs of the original field.
-/

open LatticeProb.Percolation Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5.Kesten

/-- Translating the coordinates of a translated field gives a site graph homomorphism. -/
def translateOpenSiteHom (a : PlanarCarrier) (η : PlanarCarrier → Bool) :
    siteOpenGraph (translatePlanarField a η) →g siteOpenGraph η where
  toFun z := a + z
  map_rel' {z w} h := by
    refine ⟨?_, h.2⟩
    simpa only [Prod.fst_add, Prod.snd_add, add_sub_add_left_eq_sub] using h.1

/-- Exchanging the coordinates of a swapped field gives a site graph homomorphism. -/
def swapOpenSiteHom (η : PlanarCarrier → Bool) :
    siteOpenGraph (swapPlanarField η) →g siteOpenGraph η where
  toFun := Prod.swap
  map_rel' {z w} h := by
    refine ⟨?_, h.2⟩
    simpa only [Prod.fst_swap, Prod.snd_swap, add_comm] using h.1

end Rigidity.Proofs.Section5.Kesten
