import Rigidity.Proofs.Corrector.GeneralFlipResampling

/-!
# Lemma 3.5 of Dario for the partition into good cubes of `ℤᵈ`

Lemma 3.5 of Dario: there are `C₀, C < ∞` such that for each bond `e = {x, y}` and environments
`𝐚, 𝐚̃` equal off `e`, `size(□_{𝒫(𝐚̃)}(z)) ≤ C size(□_{𝒫(𝐚)}(x))` for
`z ∈ B(x, C₀ size(□_{𝒫(𝐚)}(x)))`,
and `size(□_{𝒫(𝐚̃)}(z)) = size(□_{𝒫(𝐚)}(z))` outside that ball. Steps 1 and 2 of the proof of
Lemma 3.3 use it through the coarsened functions: outside the ball the coarsening
`[w]_{𝒫(𝐚̃)}(z) = w(z̄(□_{𝒫(𝐚̃)}(z)))` equals `[w]_{𝒫(𝐚)}(z)`, so the second clause is stated
for the partition cube and its anchor, as in the planar form `Rigidity.Corrector.ResamplePartitionBound`.
Here, for the partition of Armstrong and Dario into good cubes of `ℤᵈ` (`partitionCube`,
`partitionAnchor`):

* `InResampleBall`: the ball `{z : |z - x|_∞ < C₀ 3^k}`, `3^k` the side of `□_{𝒫(𝐚)}(x)`;
* `ResamplePartitionBound C₀ C`: the two clauses of Lemma 3.5 with constants `C₀, C`;
* `DarioResamplePartitionThree`: Lemma 3.5 in every dimension `d ≥ 3` (hypothesis; the printed
  proof lists five ingredients for Dario's partition and is a sketch);
* `partitionCube_eq_and_anchor_eq_of_resample`, `scale_le_of_resample`: its two clauses for the
  flips `ω^{e,b}` and `ω^{e,b'}` of a configuration, with the anchors `guardAnchor` of the
  corrector chain.
-/

namespace Rigidity.Corrector.GeneralDim

open LatticeProb.Percolation Rigidity.Percolation

variable {d : ℕ}

/-- The ball `{z : |z - x|_∞ < C₀ 3^k}` of Lemma 3.5 of Dario, `3^k` the side of `□_{𝒫(ω)}(x)`. -/
def InResampleBall (C₀ : ℕ) (ω : Configuration d) (x z : Vertex d) : Prop :=
  ∀ i, |z i - x i| < (C₀ : ℤ) * 3 ^ (partitionCube ω x).scale

/-- The two clauses of Lemma 3.5 of Dario for the partition into good cubes of `ℤᵈ` with constants
`C₀, C`: for each bond `e`, configurations `ω, ω'` equal off `e` on which the partition is defined,
each endpoint `x` of `e` and each `z`,

* if `|z - x|_∞ < C₀ size(□_{𝒫(ω)}(x))`, then `size(□_{𝒫(ω')}(z)) ≤ C size(□_{𝒫(ω)}(x))`;
* otherwise `□_{𝒫(ω')}(z) = □_{𝒫(ω)}(z)` and the anchors of this cube for `ω` and `ω'` agree, so
  that the coarsenings `[w]_{𝒫(ω')}(z)` and `[w]_{𝒫(ω)}(z)` agree. -/
def ResamplePartitionBound (C₀ C : ℕ) : Prop :=
  ∀ (e : Bond d) (ω ω' : Configuration d), (∀ b, b ≠ e → ω' b = ω b) →
    PartitionEvent ω → PartitionEvent ω' → ∀ x ∈ e.1, ∀ z : Vertex d,
      (InResampleBall C₀ ω x z →
        3 ^ (partitionCube ω' z).scale ≤ C * 3 ^ (partitionCube ω x).scale) ∧
      (¬ InResampleBall C₀ ω x z →
        partitionCube ω' z = partitionCube ω z ∧ partitionAnchor ω' z = partitionAnchor ω z)

/-- **Dario, Lemma 3.5, in dimension `d ≥ 3`** (hypothesis), for the partition into good cubes of
`ℤᵈ`: the bound `ResamplePartitionBound C₀ C` holds for some constants `C₀ > 0` and `C`. The printed
proof is a sketch for Dario's partition; the planar form for the partition of meshed squares is
`Rigidity.Corrector.DarioResamplePartitionTwo`. -/
def DarioResamplePartitionThree : Prop :=
  ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∃ C₀ C : ℕ, 0 < C₀ ∧ ResamplePartitionBound (d := d) C₀ C

theorem setBond_agree_off (e : Bond d) (b b' : Bool) (ω : Configuration d) :
    ∀ c, c ≠ e → setBond e b' ω c = setBond e b ω c := fun c hc => by
  simp only [setBond, Function.update_of_ne hc]

/-- The second clause of Lemma 3.5 for the flips `ω^{e,b}` and `ω^{e,b'}`: outside the ball the
partition cubes and the anchors agree. -/
theorem partitionCube_eq_and_anchor_eq_of_resample {C₀ C : ℕ}
    (h : ResamplePartitionBound (d := d) C₀ C)
    {e : Bond d} {b b' : Bool} {ω : Configuration d}
    (hP : PartitionEvent (setBond e b ω)) (hP' : PartitionEvent (setBond e b' ω))
    {x : Vertex d} (hx : x ∈ e.1) {z : Vertex d} (hz : ¬ InResampleBall C₀ (setBond e b ω) x z) :
    partitionCube (setBond e b' ω) z = partitionCube (setBond e b ω) z ∧
      guardAnchor (setBond e b' ω) z = guardAnchor (setBond e b ω) z := by
  obtain ⟨h1, h2⟩ := (h e _ _ (setBond_agree_off e b b' ω) hP hP' x hx z).2 hz
  exact ⟨h1, by rw [guardAnchor_of_event hP, guardAnchor_of_event hP', h2]⟩

/-- The first clause of Lemma 3.5 for the flips `ω^{e,b}` and `ω^{e,b'}`. -/
theorem scale_le_of_resample {C₀ C : ℕ}
    (h : ResamplePartitionBound (d := d) C₀ C)
    {e : Bond d} {b b' : Bool} {ω : Configuration d}
    (hP : PartitionEvent (setBond e b ω)) (hP' : PartitionEvent (setBond e b' ω))
    {x : Vertex d} (hx : x ∈ e.1) {z : Vertex d} (hz : InResampleBall C₀ (setBond e b ω) x z) :
    3 ^ (partitionCube (setBond e b' ω) z).scale ≤
      C * 3 ^ (partitionCube (setBond e b ω) x).scale :=
  (h e _ _ (setBond_agree_off e b b' ω) hP hP' x hx z).1 hz

end Rigidity.Corrector.GeneralDim
