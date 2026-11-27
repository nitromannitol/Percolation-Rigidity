import Rigidity.Proofs.Corrector.GeneralFlipResampling

/-!
# Lemma 3.5 of Dario for the partition into good cubes of `ℤᵈ`, in corrected form

Lemma 3.5 of Dario, as printed: there are `C₀, C < ∞` such that for each bond `e = {x, y}` and
environments `𝐚, 𝐚̃` equal off `e`, `size(□_{𝒫(𝐚̃)}(z)) ≤ C size(□_{𝒫(𝐚)}(x))` for
`z ∈ B(x, C₀ size(□_{𝒫(𝐚)}(x)))`, and `size(□_{𝒫(𝐚̃)}(z)) = size(□_{𝒫(𝐚)}(z))` outside that ball.
In dimension `d ≥ 3` this fails for the partition into good cubes: one bond can be opened or
closed in a configuration whose partition has side `27` everywhere so that the partition of the
new configuration has arbitrarily large cubes, at `x` and far from `x` (the step of the printed
proof that fails is the preservation of goodness at large scales, ingredient 3). The corrected
form, used here, replaces the scale `s = size(□_{𝒫(𝐚)}(x))` by

`S = max(size(□_{𝒫(𝐚)}(x)), size(□_{𝒫(𝐚̃)}(x)))`

in the radius of the ball and in the bound (`resampleScale`); the same near and far conclusions
then hold, with equal anchors far from the bond (proved in `GeneralResamplePartitionHolds`
with the constants `C₀ = 81`, `C = 243`, `resamplePartitionBound_holds`), and `S` has the
stretched-exponential tail of the partition sizes. Steps 1 and 2 of the proof of Lemma 3.3 use it
through the coarsened functions: outside the ball the coarsening `[w]_{𝒫(𝐚̃)}(z)` equals
`[w]_{𝒫(𝐚)}(z)`, so the second clause is stated for the partition cube and its anchor. Here:

* `resampleScale`: the scale `S`;
* `InResampleBall`: the ball `{z : |z - x|_∞ < C₀ S}`;
* `ResamplePartitionBound C₀ C`: the two clauses of the corrected Lemma 3.5 with constants `C₀, C`;
* `DarioResamplePartitionThree`: the corrected Lemma 3.5 in every dimension `d ≥ 3` (proved in
  `GeneralResamplePartitionProved`, `darioResamplePartitionThree_holds`);
* `partitionCube_eq_and_anchor_eq_of_resample`, `scale_le_of_resample`: its two clauses for the
  flips `ω^{e,b}` and `ω^{e,b'}` of a configuration, with the anchors `guardAnchor` of the
  corrector chain.
-/

namespace Rigidity.Corrector.GeneralDim

open LatticeProb.Percolation Rigidity.Percolation

variable {d : ℕ}

/-- The scale `S = max(size(□_{𝒫(ω)}(x)), size(□_{𝒫(ω')}(x)))` of the corrected Lemma 3.5. -/
noncomputable def resampleScale (ω ω' : Configuration d) (x : Vertex d) : ℕ :=
  max (3 ^ (partitionCube ω x).scale) (3 ^ (partitionCube ω' x).scale)

theorem resampleScale_comm (ω ω' : Configuration d) (x : Vertex d) :
    resampleScale ω ω' x = resampleScale ω' ω x :=
  max_comm _ _

theorem le_resampleScale_left (ω ω' : Configuration d) (x : Vertex d) :
    3 ^ (partitionCube ω x).scale ≤ resampleScale ω ω' x :=
  le_max_left _ _

theorem le_resampleScale_right (ω ω' : Configuration d) (x : Vertex d) :
    3 ^ (partitionCube ω' x).scale ≤ resampleScale ω ω' x :=
  le_max_right _ _

/-- The ball `{z : |z - x|_∞ < C₀ S}` of the corrected Lemma 3.5. -/
def InResampleBall (C₀ : ℕ) (ω ω' : Configuration d) (x z : Vertex d) : Prop :=
  ∀ i, |z i - x i| < (C₀ : ℤ) * resampleScale ω ω' x

/-- The two clauses of the corrected Lemma 3.5 of Dario for the partition into good cubes of `ℤᵈ`
with constants `C₀, C`: for each bond `e`, configurations `ω, ω'` equal off `e` on which the
partition is defined, each endpoint `x` of `e` and each `z`, with
`S = max(size(□_{𝒫(ω)}(x)), size(□_{𝒫(ω')}(x)))`,

* if `|z - x|_∞ < C₀ S`, then `size(□_{𝒫(ω')}(z)) ≤ C S`;
* otherwise `□_{𝒫(ω')}(z) = □_{𝒫(ω)}(z)` and the anchors of this cube for `ω` and `ω'` agree, so
  that the coarsenings `[w]_{𝒫(ω')}(z)` and `[w]_{𝒫(ω)}(z)` agree. -/
def ResamplePartitionBound (C₀ C : ℕ) : Prop :=
  ∀ (e : Bond d) (ω ω' : Configuration d), (∀ b, b ≠ e → ω' b = ω b) →
    PartitionEvent ω → PartitionEvent ω' → ∀ x ∈ e.1, ∀ z : Vertex d,
      (InResampleBall C₀ ω ω' x z →
        3 ^ (partitionCube ω' z).scale ≤ C * resampleScale ω ω' x) ∧
      (¬ InResampleBall C₀ ω ω' x z →
        partitionCube ω' z = partitionCube ω z ∧ partitionAnchor ω' z = partitionAnchor ω z)

/-- **Dario, Lemma 3.5, in corrected form, in dimension `d ≥ 3`** (the statement; it is proved by
`darioResamplePartitionThree_holds`), for the partition
into good cubes of `ℤᵈ`: the bound `ResamplePartitionBound C₀ C`, with the scale `S` of both
configurations at the endpoint, holds for some constants `C₀ > 0` and `C`. The printed form, with
the scale of one configuration, fails in dimension `d ≥ 3`; the planar form for the partition of
meshed squares is `Rigidity.Corrector.DarioResamplePartitionTwo`. -/
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
    {x : Vertex d} (hx : x ∈ e.1) {z : Vertex d}
    (hz : ¬ InResampleBall C₀ (setBond e b ω) (setBond e b' ω) x z) :
    partitionCube (setBond e b' ω) z = partitionCube (setBond e b ω) z ∧
      guardAnchor (setBond e b' ω) z = guardAnchor (setBond e b ω) z := by
  obtain ⟨h1, h2⟩ := (h e _ _ (setBond_agree_off e b b' ω) hP hP' x hx z).2 hz
  exact ⟨h1, by rw [guardAnchor_of_event hP, guardAnchor_of_event hP', h2]⟩

/-- The first clause of Lemma 3.5 for the flips `ω^{e,b}` and `ω^{e,b'}`. -/
theorem scale_le_of_resample {C₀ C : ℕ}
    (h : ResamplePartitionBound (d := d) C₀ C)
    {e : Bond d} {b b' : Bool} {ω : Configuration d}
    (hP : PartitionEvent (setBond e b ω)) (hP' : PartitionEvent (setBond e b' ω))
    {x : Vertex d} (hx : x ∈ e.1) {z : Vertex d}
    (hz : InResampleBall C₀ (setBond e b ω) (setBond e b' ω) x z) :
    3 ^ (partitionCube (setBond e b' ω) z).scale ≤
      C * resampleScale (setBond e b ω) (setBond e b' ω) x :=
  (h e _ _ (setBond_agree_off e b b' ω) hP hP' x hx z).1 hz

end Rigidity.Corrector.GeneralDim
