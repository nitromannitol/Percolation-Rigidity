import Rigidity.Draft.Section6Statements
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality

/-! Carving of Theorem 6.5 (slow mixing of the sandpile chain on the cluster) into steps.

Paper: `paper/percolation-harmonic-corrected.tex`, the chain
L2803-2815, the eigenvalues L2836-2858, Fig. slow-mixing-gadget L2922-2928, Theorem 6.5
L2931-2942, proof L2943-2970. The statement is `Rigidity.Section6.SlowMixingStmt`; the steps are
stated on the draft's objects (`toppling`, `SandpileGroup`, `chainLaw`, `l2DistSq`,
`IsLargestBoxCluster`, `cube`).

Steps:
* `UniqueClusterStep`: almost surely there is a unique infinite open cluster. Cited
  (Aizenman-Kesten-Newman 1987, Burton-Keane 1989), needed for the `∃ h` of the statement.
* `LargestClusterStep`: almost surely, for every large `n`, some largest open cluster of `Q_n`
  lies in `𝒞_∞` (the restriction event of paper L2805, asserted by the statement). Proposition 2.3
  with Borel-Cantelli.
* `FiniteGroupStep` (step:6.5-finite-group): proved in the paper.
* `FourierStep` (step:6.5-fourier): proved in the paper (Plancherel; Jerison-Levine-Pike Lemma 2.9).
* `DensityStep` (step:6.5-density): only its lower bound is used, and it follows from
  `GadgetCountStep` (`densityStep_of_gadgetCountStep`); the upper bound `|V| ≤ (2n+1)^d` is
  `card_le_of_isLargestBoxCluster`. Not a hypothesis of `slowMixing_of_steps`.
* `UpperBoundStep` (step:6.5-upper): GAP in the paper's proof (L2948-2951). Jerison-Levine-Pike
  Theorem 4.3 is for a simple graph and a chain adding the chip at a uniform vertex *including the
  sink*; the chain of Theorem 6.5 adds it at a uniform site of `V`, on the multigraph obtained by
  wiring the outside of `V` into a sink. For this chain the bound fails when every site of `V`
  has an even number of open edges leaving `V` (then `1/2` on `V` is harmonic mod 1, `λ = -1`).
  The step adds the hypothesis that some site of `V` has exactly one open edge leaving `V`, under
  which the proof of JLP Theorems 3.8, 4.1, 4.3 goes through with a constant depending on `d`.
* `SingleExitStep`: almost surely, for large `n`, such a site exists. Not in the paper (it repairs
  the gap above).
* `UpperTimeStep`: the calculus turning `K m log(2m(1 + 1/ε))` into `C n^d log n`. Proved in the
  paper.
* `GadgetCharacterStep` (step:6.5-gadget-characters): proved in the paper; eigenvalue `1 - 4/m`
  (C25).
* `GadgetCountStep` (step:6.5-gadget-count): cited (multiparameter ergodic theorem, with
  Proposition 2.3).
* `LowerBoundStep` (step:6.5-lower): calculus. Proved in the paper. -/

open MeasureTheory LatticeProb.Percolation Classical Filter Rigidity.Section6

namespace Rigidity.Steps.S6

variable {d : ℕ}

/-! ### Objects -/

/-- The hypotheses of Theorem 6.5 on `V` (paper L2807): `V = 𝒞_*(Q_n)` is a largest open cluster
of `Q_n`, `V ⊂ 𝒞_∞` and `V` meets `∂Q_n`. -/
def IsAdmissibleCluster (ω : Configuration d) (h : HasUniqueInfiniteOpenComponent ω) (n : ℕ)
    (V : Finset (Vertex d)) : Prop :=
  IsLargestBoxCluster ω n V ∧ (∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp) ∧
    ∃ x ∈ V, ∃ i, |x i| = (n : ℤ)

/-- The class `[1_x]` of a unit chip at `x ∈ V` in the sandpile group. -/
noncomputable def chip (ω : Configuration d) (V : Finset (Vertex d)) (x : V) :
    SandpileGroup ω V :=
  QuotientAddGroup.mk (Pi.single x 1)

/-- The eigenvalue of the chain at the character `χ` (paper (eq:eigenvalue-frequency), L2839):
`λ_χ = |V|⁻¹ Σ_{x ∈ V} χ([1_x])`. -/
noncomputable def chainEigenvalue (ω : Configuration d) (V : Finset (Vertex d))
    (χ : AddChar (SandpileGroup ω V) ℂ) : ℂ :=
  (V.card : ℂ)⁻¹ * ∑ x : V, χ (chip ω V x)

/-- The open neighbours of `x` outside `V`: the open edges at `x` along which chips leave `V`. -/
noncomputable def exitNeighbors (ω : Configuration d) (V : Finset (Vertex d)) (x : Vertex d) :
    Finset (Vertex d) :=
  ((openGraph ω).neighborFinset x).filter (· ∉ V)

/-- `a, b` are the two sites of value `1/2` of the gadget of Fig. slow-mixing-gadget: distinct,
each with exactly two open edges, to the same two sites (the other corners of the square). -/
def IsGadgetPair (ω : Configuration d) (a b : Vertex d) : Prop :=
  a ≠ b ∧ (openGraph ω).degree a = 2 ∧ (openGraph ω).degree b = 2 ∧
    ∀ y, (openGraph ω).Adj a y ↔ (openGraph ω).Adj b y

/-- The sites of `V` belonging to a gadget pair inside `V`. -/
noncomputable def gadgetSites (ω : Configuration d) (V : Finset (Vertex d)) : Finset (Vertex d) :=
  V.filter fun a => ∃ b ∈ V, IsGadgetPair ω a b

/-- The nontrivial characters with eigenvalue `1 - 4/|V|`. -/
def gadgetCharacters (ω : Configuration d) (V : Finset (Vertex d)) :
    Set (AddChar (SandpileGroup ω V) ℂ) :=
  {χ | χ ≠ 1 ∧ chainEigenvalue ω V χ = 1 - 4 / (V.card : ℂ)}

/-! ### Steps -/

/-- Almost surely there is a unique infinite open cluster `𝒞_∞` (used throughout the paper for
`p_c < p`). Cited: Aizenman-Kesten-Newman (1987), Burton-Keane (1989), with `θ(p) > 0` for
`p > p_c`. -/
def UniqueClusterStep (d : ℕ) (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw d p, HasUniqueInfiniteOpenComponent ω

/-- The restriction event of paper L2805 holds for all large `n`: almost surely, for every large
`n`, some largest open cluster `V` of `Q_n` lies in `𝒞_∞`. Proposition 2.3 (well-connectedness of
`Q_n`, so that `𝒞_*(Q_n)` is the cluster of `𝒞_∞ ∩ Q_n` crossing the box) with Borel-Cantelli. -/
def LargestClusterStep (d : ℕ) (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ᶠ n : ℕ in atTop,
    ∃ V : Finset (Vertex d), IsLargestBoxCluster ω n V ∧
      ∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp

/-- step:6.5-finite-group (paper L2829-2830, L2848). If `V` is finite and `V ⊂ 𝒞_∞`, the
sandpile group `ℤ^V / Δ_V ℤ^V` is finite: every cluster of `V` has an open edge leaving `V`
(`𝒞_∞` is infinite and connected), so `Δ_V` is nonsingular. Proved in the paper. -/
def FiniteGroupStep (d : ℕ) : Prop :=
  ∀ (ω : Configuration d) (h : HasUniqueInfiniteOpenComponent ω) (V : Finset (Vertex d)),
    (∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp) → Finite (SandpileGroup ω V)

/-- step:6.5-fourier (paper L2855-2858, Jerison-Levine-Pike Lemma 2.9). For the chain on a finite
sandpile group, `‖P^t - U‖₂² = Σ_{χ ≠ 1} |λ_χ|^{2t}`. Proved in the paper (Plancherel on a finite
abelian group; the starting point contributes a unimodular factor). -/
def FourierStep (d : ℕ) : Prop :=
  ∀ (ω : Configuration d) (V : Finset (Vertex d)), V.Nonempty → Finite (SandpileGroup ω V) →
    ∀ t : ℕ, l2DistSq ω V t =
      ∑ᶠ (χ : AddChar (SandpileGroup ω V) ℂ) (_ : χ ≠ 1), ‖chainEigenvalue ω V χ‖ ^ (2 * t)

/-- step:6.5-density, lower bound (paper (eq:perc-cluster-has-density), L2944-2947): almost
surely, for large `n`, `c n^d ≤ |V|`. Implied by `GadgetCountStep`. -/
def DensityStep (d : ℕ) (p : unitInterval) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
    ∀ᶠ n : ℕ in atTop, ∀ V : Finset (Vertex d), IsAdmissibleCluster ω h n V →
      c * (n : ℝ) ^ d ≤ V.card

/-- step:6.5-upper (paper L2948-2951), corrected: if some site of `V` has exactly one open edge
leaving `V`, then `‖P^t - U‖₂² ≤ ε` for `t ≥ K m log(2m(1 + 1/ε))`, `m = |V|`, with `K` depending
only on `d`. Route: Jerison-Levine-Pike Theorem 3.8 (`1 - |λ_h| ≥ 8‖x‖²/n`) for the chain on `V`,
the sink term being controlled through the harmonicity at the single-exit site; then their
Theorem 4.1 and Lemma 4.2 (Micciancio-Regev, Lemma 3.3), the non-sink columns of the wired
Laplacian (sink entry included) having squared norm at most `8d²`. -/
def UpperBoundStep (d : ℕ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (ω : Configuration d) (h : HasUniqueInfiniteOpenComponent ω) (n : ℕ)
    (V : Finset (Vertex d)), IsAdmissibleCluster ω h n V →
    (∃ x ∈ V, (exitNeighbors ω V x).card = 1) →
    ∀ ε : ℝ, 0 < ε → ∀ t : ℕ, K * V.card * Real.log (2 * V.card * (1 + 1 / ε)) ≤ t →
      l2DistSq ω V t ≤ ε

/-- Almost surely, for large `n`, some site of `V` has exactly one open edge leaving `V` (e.g. a
site of `V` in the relative interior of a face of `Q_n` whose outward edge is open). Repairs the
gap of step:6.5-upper; not in the paper. -/
def SingleExitStep (d : ℕ) (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ᶠ n : ℕ in atTop,
    ∀ V : Finset (Vertex d), IsAdmissibleCluster ω h n V →
      ∃ x ∈ V, (exitNeighbors ω V x).card = 1

/-- Calculus for step:6.5-upper (paper L2951): with `m ≤ (2n+1)^d`,
`K m log(2m(1 + 1/ε)) ≤ C n^d log n` for large `n`. Proved in the paper. -/
def UpperTimeStep (d : ℕ) : Prop :=
  ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
    m ≤ (2 * n + 1) ^ d →
      K * m * Real.log (2 * m * (1 + 1 / ε)) ≤ C * (n : ℝ) ^ d * Real.log n

/-- step:6.5-gadget-characters (paper L2953-2961, Fig. slow-mixing-gadget, correction C25). Each
gadget pair `a, b` in `V` gives the character `[f] ↦ (-1)^{f(a) + f(b)}` (well defined since
`Δ_V` is symmetric and `Δ_V (1_a + 1_b)/2` is integer-valued), nontrivial, with eigenvalue
`1 - 4/|V|`; distinct pairs give distinct characters, and a site lies in at most one pair whose
character is a given one, so there are at least `|gadgetSites|/2` such characters.
Proved in the paper. -/
def GadgetCharacterStep (d : ℕ) : Prop :=
  ∀ (ω : Configuration d) (V : Finset (Vertex d)), Finite (SandpileGroup ω V) →
    (gadgetSites ω V).card ≤ 2 * Nat.card (gadgetCharacters ω V)

/-- step:6.5-gadget-count (paper L2962-2964): almost surely, for large `n`, `V` contains at least
`c n^d` gadget sites. Cited: the multiparameter ergodic theorem (the gadget pattern at a site of
`𝒞_∞` has positive probability), with Proposition 2.3 (`𝒞_∞ ∩ Q_{n/2} ⊂ 𝒞_*(Q_n)`). -/
def GadgetCountStep (d : ℕ) (p : unitInterval) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
    ∀ᶠ n : ℕ in atTop, ∀ V : Finset (Vertex d), IsAdmissibleCluster ω h n V →
      c * (n : ℝ) ^ d ≤ (gadgetSites ω V).card

/-- step:6.5-lower (paper L2964-2969, correction C25c): if `m, N ≥ c₀ n^d` then
`N (1 - 4/m)^{2t} ≥ ε` for `t ≤ c n^d log n` and large `n`. Calculus, proved in the paper
(`d ≥ 1`). -/
def LowerBoundStep (d : ℕ) : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ m N t : ℕ,
    c₀ * (n : ℝ) ^ d ≤ m → c₀ * (n : ℝ) ^ d ≤ N → (t : ℝ) ≤ c * (n : ℝ) ^ d * Real.log n →
      ε ≤ N * (1 - 4 / (m : ℝ)) ^ (2 * t)

/-! ### Reductions -/

theorem mem_cube_of_reachable {ω : Configuration d} {n : ℕ} {x y : Vertex d}
    (hx : x ∈ cube d n) (h : (boxOpenGraph ω n).Reachable x y) : y ∈ cube d n := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hx
  | cons hadj _ ih => exact ih hadj.2.2

/-- The cube `Q_n` as a finset. -/
noncomputable def cubeFinset (d n : ℕ) : Finset (Vertex d) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(n : ℤ)) n

theorem mem_cubeFinset {n : ℕ} {x : Vertex d} : x ∈ cubeFinset d n ↔ x ∈ cube d n := by
  simp [cubeFinset, cube, Fintype.mem_piFinset, abs_le]

theorem card_cubeFinset (d n : ℕ) : (cubeFinset d n).card = (2 * n + 1) ^ d := by
  rw [cubeFinset, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Int.card_Icc]
  congr 1
  omega

theorem self_mem_of_isLargestBoxCluster {ω : Configuration d} {n : ℕ} {V : Finset (Vertex d)}
    (hV : IsLargestBoxCluster ω n V) : ∃ x ∈ cube d n, x ∈ V ∧
      ∀ y ∈ V, (boxOpenGraph ω n).Reachable x y := by
  obtain ⟨⟨x, hx, hVx⟩, -⟩ := hV
  refine ⟨x, hx, ?_, fun y hy => ?_⟩
  · have : x ∈ (V : Set (Vertex d)) := by rw [hVx]; exact SimpleGraph.Reachable.refl x
    exact this
  · have : y ∈ (V : Set (Vertex d)) := hy
    rw [hVx] at this
    exact this

theorem nonempty_of_isLargestBoxCluster {ω : Configuration d} {n : ℕ} {V : Finset (Vertex d)}
    (hV : IsLargestBoxCluster ω n V) : V.Nonempty := by
  obtain ⟨x, -, hxV, -⟩ := self_mem_of_isLargestBoxCluster hV
  exact ⟨x, hxV⟩

/-- `|V| ≤ |Q_n| = (2n+1)^d`. -/
theorem card_le_of_isLargestBoxCluster {ω : Configuration d} {n : ℕ} {V : Finset (Vertex d)}
    (hV : IsLargestBoxCluster ω n V) : V.card ≤ (2 * n + 1) ^ d := by
  obtain ⟨x, hx, -, hreach⟩ := self_mem_of_isLargestBoxCluster hV
  rw [← card_cubeFinset d n]
  exact Finset.card_le_card fun y hy => mem_cubeFinset.2 (mem_cube_of_reachable hx (hreach y hy))

theorem gadgetSites_subset (ω : Configuration d) (V : Finset (Vertex d)) :
    gadgetSites ω V ⊆ V :=
  Finset.filter_subset _ _

/-- The density lower bound follows from the gadget count. -/
theorem densityStep_of_gadgetCountStep {p : unitInterval} (h : GadgetCountStep d p) :
    DensityStep d p := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c, hc, ?_⟩
  filter_upwards [h] with ω hω hu
  filter_upwards [hω hu] with n hn V hV
  exact (hn V hV).trans (by exact_mod_cast Finset.card_le_card (gadgetSites_subset ω V))

/-- A finite sum over the elements satisfying `P` is at least the part over `S ⊆ {P}`, where the
summand is constant. -/
theorem card_mul_le_finsum {α : Type*} [Finite α] (P : α → Prop) (S : Set α) (f : α → ℝ) (v : ℝ)
    (hf : ∀ a, 0 ≤ f a) (hS : ∀ a ∈ S, P a ∧ f a = v) :
    (Nat.card S : ℝ) * v ≤ ∑ᶠ (a) (_ : P a), f a := by
  have := Fintype.ofFinite α
  have hsum : ∑ᶠ (a) (_ : P a), f a = ∑ a, if P a then f a else 0 := by
    rw [← finsum_eq_sum_of_fintype]
    exact finsum_congr fun a => finsum_eq_if
  rw [hsum, Nat.card_eq_card_toFinset, ← nsmul_eq_mul, ← Finset.sum_const]
  calc ∑ _a ∈ S.toFinset, v = ∑ a ∈ S.toFinset, if P a then f a else 0 :=
        Finset.sum_congr rfl fun a ha => by
          obtain ⟨hP, hfa⟩ := hS a (Set.mem_toFinset.1 ha)
          rw [if_pos hP, hfa]
    _ ≤ ∑ a, if P a then f a else 0 :=
        Finset.sum_le_univ_sum_of_nonneg fun a => by split_ifs <;> simp [hf a]

/-- The lower bound on `‖P^t - U‖₂²` from the gadget characters. -/
theorem card_gadgetCharacters_mul_le_l2DistSq (hFo : FourierStep d) {ω : Configuration d}
    {V : Finset (Vertex d)} (hV : V.Nonempty) [Finite (SandpileGroup ω V)] (t : ℕ) :
    (Nat.card (gadgetCharacters ω V) : ℝ) * (1 - 4 / (V.card : ℝ)) ^ (2 * t) ≤
      l2DistSq ω V t := by
  rw [hFo ω V hV inferInstance t]
  refine card_mul_le_finsum _ _ _ _ (fun _ => by positivity) fun χ hχ => ⟨hχ.1, ?_⟩
  have hreal : (1 : ℂ) - 4 / (V.card : ℂ) = ((1 - 4 / (V.card : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hχ.2, hreal, Complex.norm_real, Real.norm_eq_abs, (even_two_mul t).pow_abs]

/-! ### Assembly -/

/-- Theorem 6.5 from its steps. -/
theorem slowMixing_of_steps {d : ℕ} [NeZero d] (_hd : 2 ≤ d) (p : unitInterval)
    (_hpc : criticalProbability d < (p : ℝ)) (_hp1 : (p : ℝ) < 1)
    (hU : UniqueClusterStep d p) (hLC : LargestClusterStep d p) (hF : FiniteGroupStep d)
    (hFo : FourierStep d)
    (hUB : UpperBoundStep d) (hSE : SingleExitStep d p) (hUT : UpperTimeStep d)
    (hGC : GadgetCharacterStep d) (hGN : GadgetCountStep d p) (hLB : LowerBoundStep d) :
    SlowMixingStmt d p := by
  obtain ⟨K, hK, hUB⟩ := hUB
  obtain ⟨C, hC, hUT⟩ := hUT K hK
  obtain ⟨c₀, hc₀, hGN⟩ := hGN
  obtain ⟨c, hc, hLB⟩ := hLB (c₀ / 2) (by positivity)
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [hU, hLC, hSE, hGN] with ω hω hLCω hSEω hGNω
  refine ⟨hω, fun ε hε => ?_⟩
  filter_upwards [hLCω hω, hSEω hω, hGNω hω, hUT ε hε, hLB ε hε]
    with n hLCn hSEn hGNn hUTn hLBn
  refine ⟨hLCn, fun V hV hVC hVb => ?_⟩
  have hadm : IsAdmissibleCluster ω hω n V := ⟨hV, hVC, hVb⟩
  have := hF ω hω V hVC
  refine ⟨fun t ht => hUB ω hω n V hadm (hSEn V hadm) ε hε t
    ((hUTn V.card (card_le_of_isLargestBoxCluster hV)).trans ht), fun t ht => ?_⟩
  have hK := hGNn V hadm
  have hKV : ((gadgetSites ω V).card : ℝ) ≤ V.card := by
    exact_mod_cast Finset.card_le_card (gadgetSites_subset ω V)
  have hKN : ((gadgetSites ω V).card : ℝ) ≤ 2 * Nat.card (gadgetCharacters ω V) := by
    exact_mod_cast hGC ω V this
  have hn : 0 ≤ c₀ * (n : ℝ) ^ d := by positivity
  refine (hLBn V.card (Nat.card (gadgetCharacters ω V)) t (by linarith) (by linarith) ht).trans ?_
  exact card_gadgetCharacters_mul_le_l2DistSq hFo (nonempty_of_isLargestBoxCluster hV) t

end Rigidity.Steps.S6
