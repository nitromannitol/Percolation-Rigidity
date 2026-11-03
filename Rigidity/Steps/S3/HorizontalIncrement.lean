import Rigidity.Proofs.Section5.ThirdGoodEvent
import Rigidity.Proofs.Section5.ThirdGoodEventDirectionFree

/-!
# The signed variant of Proposition 3.2 (Lemma 5.25, L2370): the slit route does not give it

This file records why the printed third good event on the edge `(x, x + e₁)` (`eventG3Edge`) of
Lemma 5.25 needs a signed variant of Proposition 3.2 that the slit argument of its proof does not
give. The signed variant is proved instead by a local surgery, which proves the directional step
of the printed Lemma 5.25 (positive probability of `eventG3Edge 0 C_χ`):
`Rigidity/Steps/S3/SignedIncrement.lean`
(`horizontalIncrementStep_of_exteriorNetwork_inputs`), with the exterior network of the surgery
region proved from the literature inputs in `Rigidity/Proofs/S3/ExteriorNetwork.lean`
(`exteriorNetworkStep`). The draft third good event `G_3(x, C_χ)` is direction-free ([C32]); it
also follows from Proposition 3.2 as printed
(`Rigidity/Proofs/Section5/ThirdGoodEventDirectionFree.lean`, `thirdGoodEventStep`). This file has
no declarations; the direction-free lemmas (`neighborRise_of_notLipschitz`, the measurable subset
of `G_3`) are in `ThirdGoodEventDirectionFree.lean`.


The third good event `G_3(0, C_χ)` of Lemma 5.25 asks that `(0, e₁)` be an edge of `𝒞_∞` with
`ℓ_{e₁}(e₁) - ℓ_{e₁}(0) ≥ C_χ`, and the printed proof (L2370, L2383) takes its positive probability
from Proposition 3.2 "and symmetry arguments". The slope-`e₁` symmetries preserve the sign of a
horizontal increment, so what is needed is the signed variant `HorizontalIncrementStep`
(`Rigidity/Proofs/Section5/ThirdGoodEvent.lean`): for every `L ≥ 1`, with positive probability,
`ℓ_{e₁}(e₁) - ℓ_{e₁}(0) > L` across the edge `(0, e₁)` of `𝒞_∞`.

**The proof of Proposition 3.2 does not give the signed variant.** Argue as in Proposition 3.2
(`Rigidity/Steps/S3/NotLipschitz.lean`) by contradiction, from the signed hypothesis `H⁺(L)`:
almost surely, and by finite energy for every environment `ω'` obtained by closing finitely many
bonds, every increment `ℓ'(x + e₁) - ℓ'(x)` across an open horizontal edge of the infinite cluster
is at most `L`.
* The centre-plane count of `step:3.2-contradiction` is one-sided and survives: the flux of the new
  corrected plane `ℓ'` out of `L(Q_N)` through the centre plane is a sum of increments across the
  remaining horizontal edges, each at most `L` (bridges carry none).
* Lemma 3.3 does not survive. It writes `ℓ - ℓ'` on the left face and the sides as
  `∑_{e ∈ B} ∇∇G(·, e) V_e`, `V_e = ℓ'(x_e + e₁) - ℓ'(x_e)` the jump of `ℓ'` across the removed
  edge `e`, and the mixed derivative of the Green function has no sign. Proposition 3.2 bounds
  `|V_e| ≤ L dist_{𝒞'}(x_e, x_e + e₁) ≤ L K N^{1/2}` by the Lipschitz bound along a short path;
  under `H⁺(L)` the edges of the short path in the directions `-e₁` and `±e₂` are unbounded.
  Reopening `e` (one bond, a rank-one change) gives the increment `V_e / (1 + R_e)` across `e`,
  `R_e ≤ dist_{𝒞'}(x_e, x_e + e₁)` the effective resistance, so `H⁺(L)` bounds `V_e` from above
  only: `V_e ≤ L (1 + K N^{1/2})`. With this, the printed argument (left flux of order `N^{d-1}`,
  `∑_e |∇∇G| = O(N^{d-7/4})` from `GreenKernelSumStep`) only shows that some removed edge has
  `V_e ≤ -c N^{3/4}`, which contradicts nothing.
* Keeping one hole edge `(0, e₁)` open in the slit does not help: the flux of `ℓ'` through the hole
  is controlled by the same comparison of `ℓ'` with `ℓ`, and if every other centre edge is closed
  the short paths have length of order `N`, so even a two-sided Lipschitz bound gives a comparison
  error `O(L N^{d-3/4})`, larger than the flux `ā N^{d-1}`.
A proof of the signed variant needs an ingredient beyond the slit argument: a lower bound on the
jumps of the slit plane across the removed edges (the crack-opening displacement, of order `+N`),
or a local surgery turning a large increment of either sign along any edge into a large positive
increment along `(0, e₁)`. The local surgery is `Rigidity/Steps/S3/SignedIncrement.lean`; its new
ingredient, the exterior network of the surgery region (`ExteriorNetworkStep`), is proved from
the literature inputs in `Rigidity/Proofs/S3/ExteriorNetwork.lean`.

**What Proposition 3.2 gives.** The direction-free variant: for every `L ≥ 1`, with positive
probability the origin lies in `𝒞_∞` and has a neighbour `y` in `𝒞_∞` with `ℓ_{e₁}(y) - ℓ_{e₁}(0) > L`
(`Rigidity.Proofs.Section5.neighborRise_of_notLipschitz`). The proof of Lemma 5.27 uses the edge
`(x₀, x₀ + e₁)` of the printed `G_3(x₀, C_χ)` only as an edge of `𝒞_∞` at `x₀` across which
`ℓ_{e₁}` increases by `C_χ`, so the direction-free `G_3` of [C32] closes the gap with
Proposition 3.2 as printed; the local surgery closes it for the printed directional `G_3` as well.
-/
