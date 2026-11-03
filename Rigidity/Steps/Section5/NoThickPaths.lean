import Rigidity.Steps.Section5.LongNonzeroPaths
import Rigidity.Proofs.Section5.FiniteMaxPrinciple
import Rigidity.External.JordanCurve

/-! # Lemma 5.19: no thick paths in the zero level set

Carving of Lemma 5.19 (`NoThickPathsStmt`, corrected draft L2028-2035, proof L2037-2089, with
correction [C21]). Suppose that `supp u` is infinite, that `γ` is a bi-infinite path of `𝒞_∞` inside
`L_0 = {u = 0}` and that `u = 0` on `𝒞_∞ ∩ D` for a connected component `D` of `ℝ² \ γ`. Fix `R ≥ 1`
with `supp f ⊆ Q_R` and `γ(0) ∈ Q_R`.

* `ManyPathsStep` (step:5.19-many-paths, L2040-2043): from the loops of Lemma 5.14 and the
  nonzero paths of Lemma 5.18, for every `N` there are `N` disjoint paths `γ_k` of `𝒞_∞` outside
  `Q_{R+1}`, from a vertex `γ(m_k)` of `γ` to a vertex where `u ≠ 0`, meeting `γ` only at their
  initial point, and such that `γ` stays outside `Q_R` between `γ(m_k)` and `γ(m_l)`. A loop in
  `Q_{2m} \ Q_m` with nonzero winding number meets the path of Lemma 5.18 and `γ`; the path `γ_k` is
  the arc of the loop from the path of Lemma 5.18 back to its first vertex on `γ`. The loops at
  scales beyond `γ ∩ Q_R` meet `γ` on its two tails, and one tail carries half of them.
* `SignsStep` (step:5.19-signs, L2045-2051): let `z_k` be the last vertex of the initial zero
  stretch of `γ_k`. As `u` is harmonic at `z_k ∉ supp f`, `z_k` has neighbours `p_k`, `n_k` with
  `u(p_k) > 0 > u(n_k)`. The components of `{u > 0}` through `p_k` and of `{u < 0}` through `n_k`
  meet a pole (Lemma 5.17 for `f` and `-f`), hence a vertex `b` outside `Q_R` adjacent to it;
  pigeonhole on the pairs of such vertices of `Q_{R+1}` gives `k ≠ l` with `p_k`, `p_l` joined in
  `{u > 0} \ Q_R` and `n_k`, `n_l` joined in `{u < 0} \ Q_R`.
* `SeparationStep` (step:5.19-jordan, L2051-2089, with the Jordan curve theorem on `S²`): this
  configuration is impossible. The three arcs `A_p = z_k p_k ⋯ p_l z_l`, `A_n = z_k n_k ⋯ n_l z_l`
  and `A_z = z_k ⋯ γ(m_k) ⋯ γ(m_l) ⋯ z_l` (the zero stretches and `γ`) can be taken simple; their
  interior vertices have `u > 0`, `u < 0`, `u = 0` respectively, so they are internally disjoint
  (lattice segments meet only at lattice points) and form a theta graph: one arc lies inside the
  Jordan curve formed by the other two. The ray of `γ` from `γ(0) ∈ Q_R` away from
  `γ(m_k) ⋯ γ(m_l)` avoids the three loops, so `Q_R` lies outside each of them. If `A_n` (resp.
  `A_p`) is the inner arc, `n_k` (resp. `p_k`) lies inside `A_p ∪ A_z` (resp. `A_n ∪ A_z`) and
  is joined to a pole in `Q_R` without meeting it: impossible. If `A_z` is the inner arc, an edge
  of `γ` lies inside `A_p ∪ A_n`; every point of `γ` is in the closure of `D` (Jordan curve
  theorem on `S²` for `γ ∪ {∞}`), so the unbounded connected set `D`, which misses `A_p ∪ A_n`
  (their vertices are off `D`: `u ≠ 0` or adjacent to `p_k`, `p_l` through an edge off `γ`),
  meets the bounded inside: impossible.

Glue (proved below): Lemmas 5.14, 5.17 (for `f` and `-f`) and 5.18 hold almost surely; with
`N = |Q_{R+1}|² + 1` the three steps give the contradiction.

Lemma 2.16 (Jordan curves on `S²`, [C7]) is not used: the proof needs only the ordinary Jordan
curve theorem (`External.JordanCurveTheoremSphere`, input of `SeparationStep`).

Printed issues.
* L2040-2041: "γ(1) ∈ ∂Q_R and γ(1, …, ∞) avoids Q_R" needs `R` large enough for `γ` to meet
  `Q_R`, and `γ_i(1) ∈ γ(1, …, ∞)` is obtained only for the paths at scales beyond the finite
  stretch of `γ` between its first and last visits to `Q_R`.
* L2047-2050: `P_i` is the component of `{u > 0} \ Q_R` through `p_i`, so `p_i ∉ Q_R` is needed:
  the paths are taken outside `Q_{R+1}`. Each `P_i` contains a vertex of `Q_{R+1} \ Q_R`, so more
  than `|Q_{R+1}|²` paths suffice for the pigeonhole (the printed `C |∂Q_R|²` needs `C > 1`).
* L2083-2086: the reason given why `Q_R` is outside the loops ("some `γ_•` must intersect `𝓛`")
  is not an argument; the ray of `γ` above is. "`γ` must be disjoint from `I_z`" uses that `γ` is
  in the closure of `D`.
* L2087: "`Q_i ≠ Q_j`" should read "`N_i ≠ N_j`".
-/

open LatticeProb.Percolation Rigidity.Section5

namespace Rigidity.Steps.Section5

variable {ω : Configuration 2}

/-- The cubes `Q_r` increase with `r`. -/
theorem cube_mono {r s : ℕ} (h : r ≤ s) : cube r ⊆ cube s := fun x hx i =>
  (hx i).trans (by exact_mod_cast h)

/-- A finite set of vertices lies in a cube `Q_R` with `R ≥ 1`. -/
theorem exists_subset_cube {s : Set (Vertex 2)} (hs : s.Finite) :
    ∃ R : ℕ, 0 < R ∧ s ⊆ cube R := by
  set T := ∑ x ∈ hs.toFinset, ∑ i, (x i).natAbs
  refine ⟨T + 1, by omega, fun x hx i => ?_⟩
  have h1 : (x i).natAbs ≤ ∑ i, (x i).natAbs :=
    Finset.single_le_sum (f := fun i => (x i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have h2 : ∑ i, (x i).natAbs ≤ T :=
    Finset.single_le_sum (f := fun x : Vertex 2 => ∑ i, (x i).natAbs) (fun _ _ => Nat.zero_le _)
      (hs.mem_toFinset.mpr hx)
  rw [abs_le]
  constructor <;> omega

/-- step:5.19-many-paths (L2040-2043): given the loops around the annuli of Lemma 5.14 and the
nonzero paths of Lemma 5.18, for a bi-infinite path `γ` meeting `Q_R ⊇ supp f` and every `N`,
there are `N` disjoint paths `ρ k` of length `ℓ k` outside `Q_{R+1}`, from a vertex `γ (m k)` of
`γ` to a vertex where `u ≠ 0`, meeting `γ` only at their initial point, and such that `γ` stays
outside `Q_R` between `γ (m k)` and `γ (m l)`. -/
def ManyPathsStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (f : Vertex 2 → ℤ) (u : C → ℝ),
    (∃ M : ℕ, ∀ R : ℕ, M ≤ R → ∃ n : ℕ, ∃ β : Fin (n + 1) → C,
      (∀ i, (componentGraph C).Adj (β i) (β (i + 1))) ∧
      (∀ i, (β i).val ∈ cube (2 * R) \ cube R) ∧ windingNumber (fun i => (β i).val) ≠ 0) →
    (∀ R : ℕ, 0 < R → (∀ x, f x ≠ 0 → x ∈ cube R) → ∀ R' : ℕ, R < R' →
      ∃ n : ℕ, ∃ π : Fin (n + 1) → C,
        (∀ i : Fin n, (componentGraph C).Adj (π i.castSucc) (π i.succ)) ∧
        (π 0).val ∈ cube R ∧ (π (Fin.last n)).val ∉ cube R' ∧ ∀ i, u (π i) ≠ 0) →
    ∀ γ : ℤ → C, Function.Injective γ → (∀ n, (componentGraph C).Adj (γ n) (γ (n + 1))) →
    ∀ R : ℕ, 0 < R → (∀ x, f x ≠ 0 → x ∈ cube R) → (∃ c, (γ c).val ∈ cube R) →
    ∀ N : ℕ, ∃ (m : Fin N → ℤ) (ℓ : Fin N → ℕ) (ρ : Fin N → ℕ → C),
      (∀ k, ∀ i < ℓ k, (componentGraph C).Adj (ρ k i) (ρ k (i + 1))) ∧
      (∀ k, ρ k 0 = γ (m k)) ∧
      (∀ k i, 0 < i → i ≤ ℓ k → ρ k i ∉ Set.range γ) ∧
      (∀ k i, i ≤ ℓ k → (ρ k i).val ∉ cube (R + 1)) ∧
      (∀ k, u (ρ k (ℓ k)) ≠ 0) ∧
      (∀ k l, k ≠ l → ∀ i ≤ ℓ k, ∀ j ≤ ℓ l, ρ k i ≠ ρ l j) ∧
      ∀ k l n, min (m k) (m l) ≤ n → n ≤ max (m k) (m l) → (γ n).val ∉ cube R

/-- step:5.19-signs (L2045-2051): let `-Δu = f` with `supp f ⊆ Q_R`, every component of
`{u > 0}` and of `{-u > 0}` meeting a pole (Lemma 5.17 for `f` and `-f`). Among more than
`|Q_{R+1}|²` paths `ρ k` outside `Q_{R+1}` from a zero of `u` to a nonzero value, there are two,
`k ≠ l`, with initial zero stretches `ρ k [0, r]`, `ρ l [0, r']` whose last vertices have
neighbours `p, n` and `p', n'` such that `p` and `p'` are joined in `{u > 0} \ Q_R`, `n` and
`n'` are joined in `{u < 0} \ Q_R`, and `p` (resp. `n`) is joined to `Q_R` in `{u > 0}` (resp.
`{u < 0}`). -/
def SignsStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (f : Vertex 2 → ℤ) (u : C → ℝ),
    (∀ x, -componentLaplacian C u x = f x.val) →
    (∀ T, IsComponentOf C {x | 0 < u x} T → ∃ y ∈ T, f y.val ≠ 0) →
    (∀ T, IsComponentOf C {x | 0 < (-u) x} T → ∃ y ∈ T, (-f) y.val ≠ 0) →
    ∀ R : ℕ, (∀ x, f x ≠ 0 → x ∈ cube R) →
    ∀ N : ℕ, (cube (R + 1)).ncard ^ 2 < N →
    ∀ (ℓ : Fin N → ℕ) (ρ : Fin N → ℕ → C),
      (∀ k, ∀ i < ℓ k, (componentGraph C).Adj (ρ k i) (ρ k (i + 1))) →
      (∀ k, u (ρ k 0) = 0) → (∀ k, u (ρ k (ℓ k)) ≠ 0) →
      (∀ k i, i ≤ ℓ k → (ρ k i).val ∉ cube (R + 1)) →
    ∃ k l, k ≠ l ∧ ∃ r r' : ℕ, r ≤ ℓ k ∧ r' ≤ ℓ l ∧ (∀ i ≤ r, u (ρ k i) = 0) ∧
      (∀ i ≤ r', u (ρ l i) = 0) ∧ ∃ p n p' n' : C,
        (componentGraph C).Adj (ρ k r) p ∧ (componentGraph C).Adj (ρ k r) n ∧
        (componentGraph C).Adj (ρ l r') p' ∧ (componentGraph C).Adj (ρ l r') n' ∧
        JoinedIn C {x | 0 < u x ∧ x.val ∉ cube R} p p' ∧
        JoinedIn C {x | u x < 0 ∧ x.val ∉ cube R} n n' ∧
        (∃ y : C, y.val ∈ cube R ∧ JoinedIn C {x | 0 < u x} p y) ∧
        ∃ y : C, y.val ∈ cube R ∧ JoinedIn C {x | u x < 0} n y

/-- step:5.19-jordan (L2051-2089), from the Jordan curve theorem on `S²`: let `γ` be a
bi-infinite path in `L_0` with `u = 0` on the lattice points of a component `D` of `ℝ² \ γ`, and
`γ c ∈ Q_R`. Two disjoint paths `σ`, `σ'` in `L_0 \ Q_R`, from `γ a` and `γ b` and meeting `γ`
only there, with `γ` outside `Q_R` between `γ a` and `γ b`, cannot end at vertices with
neighbours `p, n` and `p', n'` such that `p`, `p'` are joined in `{u > 0} \ Q_R`, `n`, `n'` are
joined in `{u < 0} \ Q_R`, and `p` (resp. `n`) is joined to `Q_R` in `{u > 0}` (resp.
`{u < 0}`). -/
def SeparationStep : Prop :=
  External.JordanCurveTheoremSphere →
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (u : C → ℝ) (γ : ℤ → C), Function.Injective γ →
    (∀ n, (componentGraph C).Adj (γ n) (γ (n + 1))) → (∀ n, u (γ n) = 0) →
    ∀ z ∉ pathTrace γ, (∀ x : C,
      latticeEuclideanEmbedding x.val ∈ connectedComponentIn (pathTrace γ)ᶜ z → u x = 0) →
    ∀ (R : ℕ) (c : ℤ), (γ c).val ∈ cube R →
    ∀ a b : ℤ, (∀ n, min a b ≤ n → n ≤ max a b → (γ n).val ∉ cube R) →
    ∀ (r r' : ℕ) (σ σ' : ℕ → C),
      (∀ i < r, (componentGraph C).Adj (σ i) (σ (i + 1))) →
      (∀ i < r', (componentGraph C).Adj (σ' i) (σ' (i + 1))) →
      σ 0 = γ a → σ' 0 = γ b →
      (∀ i, 0 < i → i ≤ r → σ i ∉ Set.range γ) → (∀ i, 0 < i → i ≤ r' → σ' i ∉ Set.range γ) →
      (∀ i ≤ r, ∀ j ≤ r', σ i ≠ σ' j) →
      (∀ i ≤ r, u (σ i) = 0 ∧ (σ i).val ∉ cube R) →
      (∀ i ≤ r', u (σ' i) = 0 ∧ (σ' i).val ∉ cube R) →
    ∀ p n p' n' : C, (componentGraph C).Adj (σ r) p → (componentGraph C).Adj (σ r) n →
      (componentGraph C).Adj (σ' r') p' → (componentGraph C).Adj (σ' r') n' →
      JoinedIn C {x | 0 < u x ∧ x.val ∉ cube R} p p' →
      JoinedIn C {x | u x < 0 ∧ x.val ∉ cube R} n n' →
      (∃ y : C, y.val ∈ cube R ∧ JoinedIn C {x | 0 < u x} p y) →
      (∃ y : C, y.val ∈ cube R ∧ JoinedIn C {x | u x < 0} n y) → False

/-- Lemma 5.19 follows from Lemmas 5.14 and 5.16, the Jordan curve theorem on `S²` and the three
steps, through Lemmas 5.17 (for `f` and `-f`) and 5.18. -/
theorem noThickPaths_of_steps {p : unitInterval} {f : Vertex 2 → ℤ}
    (hJ : External.JordanCurveTheoremSphere) (h516 : StrongMaxPrincipleStmt p)
    (h514 : LoopsAroundAnnuliStmt p) (hM : ManyPathsStep) (hS : SignsStep)
    (hT : SeparationStep) : NoThickPathsStmt p f := by
  intro hf
  have hf' : (Function.support (-f)).Finite := by simpa using hf
  filter_upwards [h514, polesSuperLevelSets_of_steps Proofs.Section5.finiteMaxPrinciple h516 f hf,
    polesSuperLevelSets_of_steps Proofs.Section5.finiteMaxPrinciple h516 (-f) hf',
    longNonzeroPaths_of_steps Proofs.Section5.finiteMaxPrinciple h516 f hf]
    with ω ⟨h, hL⟩ ⟨_, hP⟩ ⟨_, hP'⟩ ⟨_, hN⟩
  refine ⟨h, fun u hu ⟨hsupp, γ, hγi, hγa, hγu, z, hz, hD⟩ => ?_⟩
  obtain ⟨R, hR0, hRs⟩ := exists_subset_cube (hf.union (Set.finite_singleton (γ 0).val))
  have hRf : ∀ x, f x ≠ 0 → x ∈ cube R := fun x hx => hRs (Or.inl hx)
  have hγ0 : (γ 0).val ∈ cube R := hRs (Or.inr rfl)
  obtain ⟨m, ℓ, ρ, hρa, hρ0, hργ, hρR, hρu, hρd, hρm⟩ := hM ω _ f u hL
    (fun R hR hRf R' hR' => hN u hu R hR hRf R' hR' hsupp) γ hγi hγa R hR0 hRf ⟨0, hγ0⟩
    ((cube (R + 1)).ncard ^ 2 + 1)
  obtain ⟨k, l, hkl, r, r', hr, hr', hu0, hu0', q, n, q', n', hq, hn, hq', hn', hqq, hnn, hqy,
      hny⟩ := hS ω _ f u hu.1 (fun T hT => hP u hu hsupp 0 T hT)
    (fun T hT => hP' (-u) (isDecayingPotential_neg hu) (by simpa using hsupp) 0 T hT) R hRf _
    (Nat.lt_succ_self _) ℓ ρ hρa (fun k => by rw [hρ0 k]; exact hγu _) hρu hρR
  have hout : ∀ k i, i ≤ ℓ k → (ρ k i).val ∉ cube R := fun k i hi hmem =>
    hρR k i hi (cube_mono (Nat.le_succ R) hmem)
  exact hT hJ ω _ u γ hγi hγa hγu z hz hD R 0 hγ0 (m k) (m l) (hρm k l) r r' (ρ k) (ρ l)
    (fun i hi => hρa k i (hi.trans_le hr)) (fun i hi => hρa l i (hi.trans_le hr'))
    (hρ0 k) (hρ0 l) (fun i hi hir => hργ k i hi (hir.trans hr))
    (fun i hi hir => hργ l i hi (hir.trans hr'))
    (fun i hi j hj => hρd k l hkl i (hi.trans hr) j (hj.trans hr'))
    (fun i hi => ⟨hu0 i hi, hout k i (hi.trans hr)⟩)
    (fun i hi => ⟨hu0' i hi, hout l i (hi.trans hr')⟩) q n q' n' hq hn hq' hn' hqq hnn hqy hny

end Rigidity.Steps.Section5
