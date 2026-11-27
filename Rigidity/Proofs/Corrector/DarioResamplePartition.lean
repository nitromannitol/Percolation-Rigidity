import Rigidity.Proofs.Corrector.DarioBondResampling
import Rigidity.Proofs.Corrector.PlanarShiftedAnchor
import PercolationClusterHomogenization.Proofs.Percolation.PlanarLocality

/-!
# Lemma 3.5 of Dario for the planar partition and the locality of the anchors

Lemma 3.5 of Dario: there are `C₀, C < ∞` such that for each bond `e = {x, y}` and environments
`𝐚, 𝐚̃` equal off `e`, `size(□_{𝒫(𝐚̃)}(z)) ≤ C size(□_{𝒫(𝐚)}(x))` for `z ∈ B(x, C₀ size(□_{𝒫(𝐚)}(x)))`,
and `size(□_{𝒫(𝐚̃)}(z)) = size(□_{𝒫(𝐚)}(z))` outside that ball. Its printed proof lists five
ingredients for Dario's partition; for the planar partition of meshed cubes it is stated here
(`DarioResamplePartitionTwo`) and proved in the module `DarioResamplePartitionHolds`
(`darioResamplePartitionTwo_holds`).

Step 1 of the proof of Lemma 3.3 uses Lemma 3.5 through the coarsened functions: outside the ball
the coarsening `[w]_{𝒫(𝐚̃)}(z) = w(z̄(□_{𝒫(𝐚̃)}(z)))` equals `[w]_{𝒫(𝐚)}(z)`. The anchors of the planar
partition depend on the bonds inside the square of side `9s` around the cube, not only on the
cube, so `DarioResamplePartitionTwo` states the second clause for the partition cube and its
anchor. Here

* `TriadicCube.planarAnchor_eq_of_adj_iff`: the anchor of a triadic cube depends only on the bonds
  inside its square of side `9s` (from the locality of meshedness and of the anchor property);
* `TriadicCube.planarAnchor_eq_of_agree_off`: changing one bond outside that square does not move
  the anchor;
* `DarioResamplePartitionTwo`: Lemma 3.5 for the planar partition, with the ball
  `{z : |z - x|_∞ < C₀ 3^k}`, `3^k` the side of `□_{𝒫(𝐚)}(x)` (proved:
  `darioResamplePartitionTwo_holds`);
* `planarPartCube_eq_and_anchor_eq_of_resample`, `scale_le_of_resample`: its two clauses for the
  flips `ω^{e,b}` and `ω^{e,¬b}` of a configuration.
-/

open LatticeProb.Percolation Rigidity.Percolation

namespace Rigidity.Percolation

variable {ω ω' : Configuration 2}

/-- **Locality of the anchor**: the anchor of a triadic cube depends only on the open edges
inside its square of side `9s`. -/
theorem TriadicCube.planarAnchor_eq_of_adj_iff {Q : TriadicCube 2}
    (hagree : ∀ x ∈ (↑Q.ninefold.vertices : Set (Vertex 2)),
      ∀ y ∈ (↑Q.ninefold.vertices : Set (Vertex 2)),
        ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y)) :
    Q.planarAnchor ω' = Q.planarAnchor ω := by
  have hm := Q.planarMeshed_iff_of_adj_iff hagree
  have hp : (fun e => Q.IsPlanarAnchor ω' (Q.center + e)) =
      fun e => Q.IsPlanarAnchor ω (Q.center + e) :=
    funext fun e => propext (Q.isPlanarAnchor_iff_of_adj_iff hagree _)
  unfold TriadicCube.planarAnchor
  by_cases h : Q.planarMeshed ω ∧ 1000 ≤ 3 ^ Q.scale
  · rw [if_pos h, if_pos ⟨hm.2 h.1, h.2⟩, hp]
  · rw [if_neg h, if_neg fun h' => h ⟨hm.1 h'.1, h'.2⟩]

/-- Configurations equal off a bond which does not lie inside a region have the same open edges
in that region. -/
theorem adj_iff_of_agree_off {e : Bond 2} (h : ∀ b, b ≠ e → ω' b = ω b) {S : Set (Vertex 2)}
    (he : e ∉ localBonds S) :
    ∀ x ∈ S, ∀ y ∈ S, ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y) :=
  adj_iff_of_localBonds fun b hb => (h b fun hbe => he (hbe ▸ hb)).symm

/-- Changing one bond outside the square of side `9s` of a cube does not move its anchor. -/
theorem TriadicCube.planarAnchor_eq_of_agree_off {Q : TriadicCube 2} {e : Bond 2}
    (h : ∀ b, b ≠ e → ω' b = ω b) (he : e ∉ localBonds (↑Q.ninefold.vertices : Set (Vertex 2))) :
    Q.planarAnchor ω' = Q.planarAnchor ω :=
  Q.planarAnchor_eq_of_adj_iff (adj_iff_of_agree_off h he)

end Rigidity.Percolation

namespace Rigidity.Corrector

/-- The ball `{z : |z - x|_∞ < C₀ 3^k}` of Lemma 3.5 of Dario, `3^k` the side of `□_{𝒫(ω)}(x)`. -/
def InResampleBall (C₀ : ℕ) (ω : Configuration 2) (x z : Vertex 2) : Prop :=
  ∀ i, |z i - x i| < (C₀ : ℤ) * 3 ^ (planarPartCube ω x).scale

/-- The two clauses of Lemma 3.5 of Dario for the planar partition with constants `C₀, C`: for each
bond `e`, configurations `ω, ω'` equal off `e` on which the partition is defined, each endpoint `x`
of `e` and each `z`,

* if `|z - x|_∞ < C₀ size(□_{𝒫(ω)}(x))`, then `size(□_{𝒫(ω')}(z)) ≤ C size(□_{𝒫(ω)}(x))`;
* otherwise `□_{𝒫(ω')}(z) = □_{𝒫(ω)}(z)` (equivalently, the sizes agree) and the anchors of this
  cube for `ω` and `ω'` agree, so that the coarsenings `[w]_{𝒫(ω')}(z)` and `[w]_{𝒫(ω)}(z)` agree. -/
def ResamplePartitionBound (C₀ C : ℕ) : Prop :=
  ∀ (e : Bond 2) (ω ω' : Configuration 2), (∀ b, b ≠ e → ω' b = ω b) →
    PlanarPartitionEvent ω → PlanarPartitionEvent ω' → ∀ x ∈ e.1, ∀ z : Vertex 2,
      (InResampleBall C₀ ω x z →
        3 ^ (planarPartCube ω' z).scale ≤ C * 3 ^ (planarPartCube ω x).scale) ∧
      (¬ InResampleBall C₀ ω x z →
        planarPartCube ω' z = planarPartCube ω z ∧ planarCoarseAnchor ω' z = planarCoarseAnchor ω z)

/-- **Dario, Lemma 3.5, for the planar partition** (the printed proof is for Dario's partition): the
bound `ResamplePartitionBound C₀ C` holds for some constants `C₀ > 0` and `C`. It holds
(`darioResamplePartitionTwo_holds`, with `C₀ = 4747`, `C = 14244`). -/
def DarioResamplePartitionTwo : Prop :=
  ∃ C₀ C : ℕ, 0 < C₀ ∧ ResamplePartitionBound C₀ C

theorem setBond_agree_off (e : Bond 2) (b b' : Bool) (ω : Configuration 2) :
    ∀ c, c ≠ e → setBond e b' ω c = setBond e b ω c := fun c hc => by
  simp only [setBond, Function.update_of_ne hc]

/-- The second clause of Lemma 3.5 for the flips `ω^{e,b}` and `ω^{e,b'}`: outside the ball the
partition cubes and the anchors agree. -/
theorem planarPartCube_eq_and_anchor_eq_of_resample {C₀ C : ℕ}
    (h : ResamplePartitionBound C₀ C)
    {e : Bond 2} {b b' : Bool} {ω : Configuration 2}
    (hP : PlanarPartitionEvent (setBond e b ω)) (hP' : PlanarPartitionEvent (setBond e b' ω))
    {x : Vertex 2} (hx : x ∈ e.1) {z : Vertex 2} (hz : ¬ InResampleBall C₀ (setBond e b ω) x z) :
    planarPartCube (setBond e b' ω) z = planarPartCube (setBond e b ω) z ∧
      guardAnchor (setBond e b' ω) z = guardAnchor (setBond e b ω) z := by
  obtain ⟨h1, h2⟩ := (h e _ _ (setBond_agree_off e b b' ω) hP hP' x hx z).2 hz
  exact ⟨h1, by rw [guardAnchor_of_event hP, guardAnchor_of_event hP', h2]⟩

/-- The first clause of Lemma 3.5 for the flips `ω^{e,b}` and `ω^{e,b'}`. -/
theorem scale_le_of_resample {C₀ C : ℕ}
    (h : ResamplePartitionBound C₀ C)
    {e : Bond 2} {b b' : Bool} {ω : Configuration 2}
    (hP : PlanarPartitionEvent (setBond e b ω)) (hP' : PlanarPartitionEvent (setBond e b' ω))
    {x : Vertex 2} (hx : x ∈ e.1) {z : Vertex 2} (hz : InResampleBall C₀ (setBond e b ω) x z) :
    3 ^ (planarPartCube (setBond e b' ω) z).scale ≤
      C * 3 ^ (planarPartCube (setBond e b ω) x).scale :=
  (h e _ _ (setBond_agree_off e b b' ω) hP hP' x hx z).1 hz

end Rigidity.Corrector
