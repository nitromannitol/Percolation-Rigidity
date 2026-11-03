import Rigidity.Steps.Section5.NoThickPaths
import Rigidity.Proofs.Section5.Separation.Theta
import Rigidity.Proofs.Section5.Separation.Chain

/-!
# Lemma 5.19: the separation step

This file proves `SeparationStep` (`step:5.19-jordan`, corrected draft L2051-2089) from the
Jordan curve theorem on `S²` (`External.JordanCurveTheoremSphere`).

Let `P = σ r` and `Q = σ' r'` be the last vertices of the two zero stretches. Three arcs of `𝒞_∞`
join `P` to `Q`, made simple (`exists_isSimpleChain`):

* `A_p = P, p ⋯ p', Q` through `{u > 0} \ Q_R`, and `A_n = P, n ⋯ n', Q` through `{u < 0} \ Q_R`
  (`chainBracket`);
* `A_z = P ⋯ σ 0 = γ a ⋯ γ b = σ' 0 ⋯ Q` along the zero stretches and `γ` (`chainAppend`).

Their interior vertices have `u > 0`, `u < 0`, `u = 0` respectively, so they meet only at `P`,
`Q`; as unit lattice segments meet only at lattice points, their traces `K_p, K_n, K_z` meet only
at `P`, `Q` (`arcTrace_inter_subset`), and any two of them form a Jordan curve
(`exists_jordanSides_of_arcs`, through `exists_path_cycle`). The theta graph lemma
(`false_of_theta`) gives the contradiction once every open arc is outside the curve formed by
the two others, as seen from `w = γ c ∈ Q_R`:

* the square `[-R, R]²` and the ray of `γ` from `γ c` away from `γ a ⋯ γ b` (`exists_ray`) miss
  the three arcs and are unbounded, hence outside each curve;
* `n` is joined to `Q_R` in `{u < 0}`, a path missing `K_p ∪ K_z`, so `A_n` is outside; same for
  `p` and `A_p`;
* a point `x` in the middle of the edge `γ a γ(a ± 1)` of `A_z` lies in the closure of the side
  `D` of `γ` (Jordan curve theorem for `γ ∪ {∞}`, `closure_connectedComponentIn_of_sphere`); `D`
  accumulates at `∞` and misses `K_p ∪ K_n` (`hD` and `latticePoint_mem_connectedComponentIn`:
  the interior vertices of `A_p`, `A_n` have `u ≠ 0`), so `D`, hence `x`, is outside `K_p ∪ K_n`.
-/

open Set Topology LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5
  Rigidity.External

namespace Rigidity.Proofs.Section5

variable {ω : Configuration 2} {C : OpenComponent ω}

theorem adj_val {x y : C} (h : (componentGraph C).Adj x y) :
    (nearestNeighborGraph 2).Adj x.val y.val :=
  openGraph_le ω h

/-- A path inside `S` gives a simple chain inside `S`. -/
theorem exists_isSimpleChain_of_joinedIn {S : Set C} {x y : C} (h : JoinedIn C S x y) :
    ∃ (f : ℤ → C) (ℓ : ℕ), f 0 = x ∧ f ℓ = y ∧ IsSimpleChain (componentGraph C) f ℓ ∧
      ∀ k, f k ∈ S := by
  obtain ⟨hx, hy, ⟨w⟩⟩ := h
  obtain ⟨f, ℓ, h0, h1, hf, -⟩ := exists_isSimpleChain w
  exact ⟨fun k => (f k).val, ℓ, by simp [h0], by simp [h1],
    ⟨fun k h0 h1 => hf.adj k h0 h1, fun k k' a b c d e => hf.inj k k' a b c d (Subtype.ext e)⟩,
    fun k => (f k).2⟩

/-- The vertices of a finite chain are joined inside the set of these vertices. -/
theorem joinedIn_of_chain (σ : ℕ → C) (r : ℕ)
    (hσ : ∀ i < r, (componentGraph C).Adj (σ i) (σ (i + 1))) :
    JoinedIn C {x | ∃ i ≤ r, σ i = x} (σ 0) (σ r) := by
  refine ⟨⟨0, Nat.zero_le _, rfl⟩, ⟨r, le_rfl, rfl⟩, ?_⟩
  suffices h : ∀ i (hi : i ≤ r), ((componentGraph C).induce {x | ∃ i ≤ r, σ i = x}).Reachable
      ⟨σ 0, ⟨0, Nat.zero_le _, rfl⟩⟩ ⟨σ i, ⟨i, hi, rfl⟩⟩ from h r le_rfl
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih => exact (ih (by omega)).trans (SimpleGraph.Adj.reachable (hσ i (by omega)))

/-! ### Arcs of `𝒞_∞` in the plane -/

/-- The trace in the plane of a chain of `𝒞_∞` on `[0, L]`. -/
def arcTrace (X : ℤ → C) (L : ℕ) : Set Plane := chainTrace (Subtype.val ∘ X) (Ico 0 L)

/-- The interior of the arc of a chain of `𝒞_∞` on `[0, L]`: the image of `(0, L)`. -/
def arcInterior (X : ℤ → C) (L : ℕ) : Set Plane :=
  polyline (latticePoint ∘ (Subtype.val ∘ X)) '' Ioo 0 L

theorem IsSimpleChain.adj_val {X : ℤ → C} {L : ℕ} (hX : IsSimpleChain (componentGraph C) X L) :
    ∀ n ∈ Ico (0 : ℤ) L, (nearestNeighborGraph 2).Adj ((Subtype.val ∘ X) n)
      ((Subtype.val ∘ X) (n + 1)) :=
  fun n hn => Rigidity.Proofs.Section5.adj_val (hX.adj n hn.1 hn.2)

theorem floor_mem_Ico {s : ℝ} {L : ℕ} (h0 : 0 ≤ s) (h1 : s < L) : 0 ≤ ⌊s⌋ ∧ ⌊s⌋ < L :=
  ⟨Int.floor_nonneg.2 h0, Int.floor_lt.2 (by exact_mod_cast h1)⟩

theorem arcInterior_subset (X : ℤ → C) (L : ℕ) : arcInterior X L ⊆ arcTrace X L := by
  rintro _ ⟨s, ⟨h0, h1⟩, rfl⟩
  exact polyline_mem_chainTrace _ (floor_mem_Ico h0.le h1)

theorem arcTrace_subset (X : ℤ → C) {L : ℕ} (hL : 0 < L) :
    arcTrace X L ⊆ arcInterior X L ∪ {latticePoint (X 0).val, latticePoint (X L).val} := by
  have himg := polyline_image_Icc (Subtype.val ∘ X) (a := 0) (b := L) (by omega)
  push_cast at himg
  rw [arcTrace, ← himg]
  rintro _ ⟨s, ⟨h0, h1⟩, rfl⟩
  rcases h0.lt_or_eq with h0 | rfl
  · rcases h1.lt_or_eq with h1 | rfl
    · exact Or.inl ⟨s, ⟨h0, h1⟩, rfl⟩
    · right; right
      have := polyline_intCast (latticePoint ∘ (Subtype.val ∘ X)) L
      push_cast at this
      rw [this]
      rfl
  · right; left
    have := polyline_intCast (latticePoint ∘ (Subtype.val ∘ X)) 0
    push_cast at this
    rw [this]
    rfl

theorem isPreconnected_arcInterior (X : ℤ → C) (L : ℕ) : IsPreconnected (arcInterior X L) :=
  isPreconnected_Ioo.image _ (continuous_polyline _).continuousOn

theorem latticePoint_mem_arcInterior (X : ℤ → C) {L : ℕ} {k : ℤ} (h0 : 0 < k) (h1 : k < L) :
    latticePoint (X k).val ∈ arcInterior X L :=
  ⟨k, ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩, polyline_intCast _ k⟩

/-- The interior of an arc misses a set meeting the arc only at its endpoints. -/
theorem disjoint_arcInterior {X : ℤ → C} {L : ℕ} (hX : IsSimpleChain (componentGraph C) X L)
    {J : Set Plane}
    (hJ : arcTrace X L ∩ J ⊆ {latticePoint (X 0).val, latticePoint (X L).val}) :
    Disjoint (arcInterior X L) J := by
  rw [Set.disjoint_left]
  rintro _ ⟨s, ⟨h0, h1⟩, rfl⟩ hJs
  have hfl := floor_mem_Ico h0.le h1
  have hadj := hX.adj_val ⌊s⌋ ⟨hfl.1, hfl.2⟩
  rcases hJ ⟨polyline_mem_chainTrace _ hfl, hJs⟩ with h | h
  · obtain ⟨e, hf⟩ := polyline_eq_latticePoint hadj h
    have := hX.inj 0 ⌊s⌋ le_rfl (by omega) hfl.1 hfl.2.le (Subtype.ext e)
    have hs := Int.floor_add_fract s
    rw [hf, ← this] at hs
    push_cast at hs
    linarith
  · obtain ⟨e, hf⟩ := polyline_eq_latticePoint hadj h
    have := hX.inj L ⌊s⌋ (by omega) le_rfl hfl.1 hfl.2.le (Subtype.ext e)
    omega

theorem exists_of_mem_chainVerts {X : ℤ → C} {L : ℕ} {z : Vertex 2}
    (hz : z ∈ chainVerts (Subtype.val ∘ X) (Ico 0 L)) :
    ∃ k : ℤ, 0 ≤ k ∧ k ≤ L ∧ z = (X k).val := by
  obtain ⟨k, ⟨h0, h1⟩, h | h⟩ := hz
  · exact ⟨k, h0, h1.le, h⟩
  · exact ⟨k + 1, by omega, by omega, h⟩

/-- Two arcs from `X 0` to `X L` meeting only at their endpoints, the first of length at least
two: their traces meet only at the endpoints. -/
theorem arcTrace_inter_subset {X Y : ℤ → C} {L M : ℕ}
    (hX : IsSimpleChain (componentGraph C) X L) (hY : IsSimpleChain (componentGraph C) Y M)
    (hL : 2 ≤ L)
    (hth : ∀ k k' : ℤ, 0 ≤ k → k ≤ L → 0 ≤ k' → k' ≤ M → X k = Y k' →
      (k = 0 ∧ k' = 0) ∨ (k = L ∧ k' = M)) :
    arcTrace X L ∩ arcTrace Y M ⊆ {latticePoint (X 0).val, latticePoint (X L).val} := by
  rintro v ⟨hv, hv'⟩
  have hne : ∀ n ∈ Ico (0 : ℤ) L, ∀ n' ∈ Ico (0 : ℤ) M,
      ¬ (((Subtype.val ∘ X) n = (Subtype.val ∘ Y) n' ∧
        (Subtype.val ∘ X) (n + 1) = (Subtype.val ∘ Y) (n' + 1)) ∨
        ((Subtype.val ∘ X) n = (Subtype.val ∘ Y) (n' + 1) ∧
        (Subtype.val ∘ X) (n + 1) = (Subtype.val ∘ Y) n')) := by
    rintro n ⟨h0, h1⟩ n' ⟨h0', h1'⟩ (⟨e1, e2⟩ | ⟨e1, -⟩)
    · have := hth _ _ h0 h1.le h0' h1'.le (Subtype.ext e1)
      have := hth _ _ (by omega) h1 (by omega) h1' (Subtype.ext e2)
      omega
    · have := hth _ _ h0 h1.le (by omega) h1' (Subtype.ext e1)
      omega
  obtain ⟨z, ⟨hz, hz'⟩, rfl⟩ := mem_chainTrace_inter hX.adj_val hY.adj_val hne hv hv'
  obtain ⟨k, hk0, hk1, rfl⟩ := exists_of_mem_chainVerts hz
  obtain ⟨k', hk0', hk1', e⟩ := exists_of_mem_chainVerts hz'
  rcases hth k k' hk0 hk1 hk0' hk1' (Subtype.ext e) with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Two arcs from `X 0 = Y 0` to `X L = Y M` meeting only at their endpoints form a Jordan
curve. -/
theorem exists_jordanSides_of_arcs (hJ : JordanCurveTheoremSphere) {X Y : ℤ → C} {L M : ℕ}
    (hX : IsSimpleChain (componentGraph C) X L) (hY : IsSimpleChain (componentGraph C) Y M)
    (h0 : X 0 = Y 0) (hLM : X L = Y M) (h3 : 3 ≤ L + M)
    (hth : ∀ k k' : ℤ, 0 ≤ k → k ≤ L → 0 ≤ k' → k' ≤ M → X k = Y k' →
      (k = 0 ∧ k' = 0) ∨ (k = L ∧ k' = M)) :
    ∃ I O, JordanSides (arcTrace X L ∪ arcTrace Y M) I O := by
  have hcj : X L = chainRev Y M 0 := by simp [chainRev, hLM]
  have hYr := hY.rev
  set c := chainAppend X L (chainRev Y M) with hc
  have hval : ∀ k : ℤ, (L : ℤ) ≤ k → c k = Y (M - (k - L)) := fun k hk => by
    rw [hc, chainAppend_of_ge hcj hk]
    rfl
  have hcm : (Subtype.val ∘ c) ((L + M : ℕ) : ℤ) = (Subtype.val ∘ c) 0 := by
    show (c _).val = (c 0).val
    rw [hval _ (by push_cast; omega), hc, chainAppend_of_le (by omega),
      show (M : ℤ) - (((L + M : ℕ) : ℤ) - L) = 0 by push_cast; ring, h0]
  have hadj : ∀ k : ℤ, 0 ≤ k → k < ((L + M : ℕ) : ℤ) →
      (nearestNeighborGraph 2).Adj ((Subtype.val ∘ c) k) ((Subtype.val ∘ c) (k + 1)) := by
    intro k hk0 hk1
    push_cast at hk1
    by_cases hk : k < L
    · simp only [Function.comp, hc]
      rw [chainAppend_of_le hk.le, chainAppend_of_le (by omega)]
      exact Rigidity.Proofs.Section5.adj_val (hX.adj k hk0 hk)
    · simp only [Function.comp]
      rw [hc, chainAppend_of_ge hcj (by omega), chainAppend_of_ge hcj (by omega),
        show k + 1 - L = k - L + 1 by ring]
      exact Rigidity.Proofs.Section5.adj_val (hYr.adj _ (by omega) (by omega))
  have hinj : ∀ k k' : ℤ, 0 ≤ k → k < ((L + M : ℕ) : ℤ) → 0 ≤ k' → k' < ((L + M : ℕ) : ℤ) →
      (Subtype.val ∘ c) k = (Subtype.val ∘ c) k' → k = k' := by
    intro k k' hk0 hk1 hk0' hk1' e
    push_cast at hk1 hk1'
    have e' : c k = c k' := Subtype.ext e
    by_cases hk : k ≤ L <;> by_cases hk' : k' ≤ L
    · rw [hc, chainAppend_of_le hk, chainAppend_of_le hk'] at e'
      exact hX.inj _ _ hk0 hk hk0' hk' e'
    · rw [hc, chainAppend_of_le hk, chainAppend_of_ge hcj (by omega)] at e'
      have := hth _ _ hk0 hk (by omega) (by omega) e'
      omega
    · rw [hc, chainAppend_of_ge hcj (by omega), chainAppend_of_le hk'] at e'
      have := hth _ _ hk0' hk' (by omega) (by omega) e'.symm
      omega
    · rw [hc, chainAppend_of_ge hcj (by omega), chainAppend_of_ge hcj (by omega)] at e'
      have := hYr.inj _ _ (by omega) (by omega) (by omega) (by omega) e'
      omega
  obtain ⟨q, β, hβ, hr⟩ := exists_path_cycle h3 hcm hadj hinj
  refine exists_jordanSides hJ β hβ ?_
  rw [hr]
  congr 1
  rw [arcTrace, arcTrace, ← chainTrace_chainRev Subtype.val Y M]
  exact chainTrace_chainAppend Subtype.val hcj

/-- The theta condition for the arc `x, f, y` and an arc from `x` to `y` avoiding the values
of `f`. -/
theorem theta_of_bracket {x y : C} {f Y : ℤ → C} {ℓ M : ℕ}
    (hY : IsSimpleChain (componentGraph C) Y M) (hY0 : Y 0 = x) (hYM : Y M = y)
    (hfY : ∀ j k' : ℤ, 0 ≤ j → j ≤ ℓ → 0 ≤ k' → k' ≤ M → f j ≠ Y k') :
    ∀ k k' : ℤ, 0 ≤ k → k ≤ ((ℓ + 2 : ℕ) : ℤ) → 0 ≤ k' → k' ≤ M →
      chainBracket x f ℓ y k = Y k' → (k = 0 ∧ k' = 0) ∨ (k = ((ℓ + 2 : ℕ) : ℤ) ∧ k' = M) := by
  intro k k' h0 h1 h0' h1' e
  push_cast at h1 ⊢
  rcases h0.lt_or_eq with h0 | rfl
  · by_cases hk : k ≤ ℓ + 1
    · rw [chainBracket_mid x f ℓ y h0 hk] at e
      exact absurd e (hfY _ _ (by omega) (by omega) h0' h1')
    · have hk2 : k = ((ℓ + 2 : ℕ) : ℤ) := by push_cast; omega
      rw [hk2, chainBracket_last, ← hYM] at e
      have := hY.inj _ _ (by omega) le_rfl h0' h1' e
      push_cast at hk2
      exact Or.inr ⟨hk2, this.symm⟩
  · rw [chainBracket_zero, ← hY0] at e
    have := hY.inj _ _ le_rfl (by omega) h0' h1' e
    exact Or.inl ⟨rfl, this.symm⟩

theorem theta_symm {X Y : ℤ → C} {L M : ℕ}
    (hth : ∀ k k' : ℤ, 0 ≤ k → k ≤ L → 0 ≤ k' → k' ≤ M → X k = Y k' →
      (k = 0 ∧ k' = 0) ∨ (k = L ∧ k' = M)) :
    ∀ k k' : ℤ, 0 ≤ k → k ≤ M → 0 ≤ k' → k' ≤ L → Y k = X k' →
      (k = 0 ∧ k' = 0) ∨ (k = M ∧ k' = L) := by
  intro k k' h0 h1 h0' h1' e
  rcases hth k' k h0' h1' h0 h1 e.symm with ⟨h, h'⟩ | ⟨h, h'⟩
  · exact Or.inl ⟨h', h⟩
  · exact Or.inr ⟨h', h⟩

theorem chainBracket_cases (x : C) (f : ℤ → C) (ℓ : ℕ) (y : C) {k : ℤ} (h0 : 0 ≤ k)
    (h1 : k ≤ ((ℓ + 2 : ℕ) : ℤ)) :
    chainBracket x f ℓ y k = x ∨ chainBracket x f ℓ y k = y ∨
      ∃ j : ℤ, 0 ≤ j ∧ j ≤ ℓ ∧ chainBracket x f ℓ y k = f j := by
  push_cast at h1
  rcases h0.lt_or_eq with h0 | rfl
  · by_cases hk : k ≤ ℓ + 1
    · exact Or.inr (Or.inr ⟨k - 1, by omega, by omega, chainBracket_mid x f ℓ y h0 hk⟩)
    · have hk2 : k = ((ℓ + 2 : ℕ) : ℤ) := by push_cast; omega
      rw [hk2, chainBracket_last]
      exact Or.inr (Or.inl rfl)
  · exact Or.inl (chainBracket_zero x f ℓ y)

theorem disjoint_arcTrace_realCube {X : ℤ → C} {L : ℕ}
    (hX : IsSimpleChain (componentGraph C) X L) {R : ℕ}
    (hR : ∀ k : ℤ, 0 ≤ k → k ≤ L → (X k).val ∉ cube R) :
    Disjoint (arcTrace X L) (realCube R) := by
  rw [Set.disjoint_left]
  intro v hv hvR
  simp only [arcTrace, chainTrace, mem_iUnion] at hv
  obtain ⟨k, ⟨h0, h1⟩, hv⟩ := hv
  exact (disjoint_edgeSegment_realCube (hX.adj_val k ⟨h0, h1⟩) (hR k h0 h1.le)
    (hR (k + 1) (by omega) (by omega))).ne_of_mem hv hvR rfl

/-- Arcs without common vertices have disjoint traces. -/
theorem disjoint_arcTrace {X Y : ℤ → C} {L M : ℕ} (hX : IsSimpleChain (componentGraph C) X L)
    (hY : IsSimpleChain (componentGraph C) Y M)
    (hd : ∀ k k' : ℤ, 0 ≤ k → k ≤ L → 0 ≤ k' → k' ≤ M → X k ≠ Y k') :
    Disjoint (arcTrace X L) (arcTrace Y M) := by
  refine disjoint_chainTrace hX.adj_val hY.adj_val (Set.disjoint_left.2 fun z hz hz' => ?_)
  obtain ⟨k, hk0, hk1, rfl⟩ := exists_of_mem_chainVerts hz
  obtain ⟨k', hk0', hk1', e⟩ := exists_of_mem_chainVerts hz'
  exact hd k k' hk0 hk1 hk0' hk1' (Subtype.ext e)

theorem latticePoint_not_mem_arcTrace {Y : ℤ → C} {M : ℕ}
    (hY : IsSimpleChain (componentGraph C) Y M) {y : C}
    (hy : ∀ k' : ℤ, 0 ≤ k' → k' ≤ M → y ≠ Y k') : latticePoint y.val ∉ arcTrace Y M := by
  intro h
  obtain ⟨k', hk0', hk1', e⟩ := exists_of_mem_chainVerts (latticePoint_mem_chainTrace hY.adj_val h)
  exact hy k' hk0' hk1' (Subtype.ext e)

theorem polyline_image_Icc_subset (g : ℤ → Vertex 2) (m : ℕ) :
    polyline (latticePoint ∘ g) '' Icc 0 (m : ℝ) ⊆ chainTrace g (Ico 0 m) ∪ {latticePoint (g m)} := by
  rintro _ ⟨s, ⟨h0, h1⟩, rfl⟩
  rcases h1.lt_or_eq with h1 | rfl
  · exact Or.inl (polyline_mem_chainTrace _ (floor_mem_Ico h0 h1))
  · right
    have := polyline_intCast (latticePoint ∘ g) m
    push_cast at this
    exact this

theorem pathTrace_eq_chainTrace (γ : ℤ → C) :
    pathTrace γ = chainTrace (Subtype.val ∘ γ) univ := by
  ext v
  simp [pathTrace, chainTrace, edgeSegment, latticePoint]

/-- The ray of `γ` from `γ c` away from the indices `[lo, hi]`. -/
theorem exists_ray {γ : ℤ → C} (hγi : Function.Injective γ) {c lo hi : ℤ}
    (hc : c < lo ∨ hi < c) :
    ∃ (Ray : Set Plane) (F : Set ℤ), IsPreconnected Ray ∧ latticePoint (γ c).val ∈ Ray ∧
      ¬ Bornology.IsBounded Ray ∧ Ray ⊆ chainTrace (Subtype.val ∘ γ) F ∧
      ∀ m ∈ F, m + 1 < lo ∨ hi < m := by
  have hinj : Function.Injective (Subtype.val ∘ γ) := Subtype.val_injective.comp hγi
  have hp := continuous_polyline (latticePoint ∘ (Subtype.val ∘ γ))
  have hint : ∀ m : ℤ, polyline (latticePoint ∘ (Subtype.val ∘ γ)) m = latticePoint (γ m).val :=
    fun m => polyline_intCast _ m
  rcases hc with hc | hc
  · refine ⟨polyline (latticePoint ∘ (Subtype.val ∘ γ)) '' Iic (c : ℝ), Iio c,
      isPreconnected_Iic.image _ hp.continuousOn, ⟨c, self_mem_Iic, hint c⟩, ?_, ?_,
      fun m hm => Or.inl (by simp only [mem_Iio] at hm; omega)⟩
    · refine fun hb => not_isBounded_image hinj (Set.Iic_infinite c) (hb.subset ?_)
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨m, show (m : ℝ) ≤ c by exact_mod_cast (show m ≤ c from hm), hint m⟩
    · rintro _ ⟨s, hs, rfl⟩
      rcases (show s ≤ c from hs).lt_or_eq with hs | rfl
      · exact polyline_mem_chainTrace _ (show ⌊s⌋ < c from Int.floor_lt.2 hs)
      · rw [hint]
        refine mem_biUnion (x := c - 1) (show c - 1 < c by omega) ?_
        simpa using right_mem_edgeSegment (γ (c - 1)).val (γ c).val
  · refine ⟨polyline (latticePoint ∘ (Subtype.val ∘ γ)) '' Ici (c : ℝ), Ici c,
      isPreconnected_Ici.image _ hp.continuousOn, ⟨c, self_mem_Ici, hint c⟩, ?_, ?_,
      fun m hm => Or.inr (by simp only [mem_Ici] at hm; omega)⟩
    · refine fun hb => not_isBounded_image hinj (Set.Ici_infinite c) (hb.subset ?_)
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨m, show (c : ℝ) ≤ m by exact_mod_cast (show c ≤ m from hm), hint m⟩
    · rintro _ ⟨s, hs, rfl⟩
      exact polyline_mem_chainTrace _ (show c ≤ ⌊s⌋ from Int.le_floor.2 hs)

/-- A component of the complement of the trace of `γ` on which `u` vanishes misses the trace of
an arc whose interior vertices have `u ≠ 0`, `γ` lying in `{u = 0}`. -/
theorem disjoint_arcTrace_component {γ : ℤ → C} {u : C → ℝ} (hγu : ∀ m, u (γ m) = 0)
    (hγa : ∀ n, (componentGraph C).Adj (γ n) (γ (n + 1))) {z₀ : Plane}
    (hD : ∀ x : C, latticePoint x.val ∈ connectedComponentIn (pathTrace γ)ᶜ z₀ → u x = 0)
    {X : ℤ → C} {L : ℕ} (hX : IsSimpleChain (componentGraph C) X L) (hL : 2 ≤ L)
    (hXu : ∀ k : ℤ, 0 < k → k < L → u (X k) ≠ 0) :
    Disjoint (arcTrace X L) (connectedComponentIn (pathTrace γ)ᶜ z₀) := by
  rw [pathTrace_eq_chainTrace] at hD ⊢
  have hγ : ∀ n ∈ (univ : Set ℤ), (nearestNeighborGraph 2).Adj ((Subtype.val ∘ γ) n)
      ((Subtype.val ∘ γ) (n + 1)) := fun n _ => adj_val (hγa n)
  have hoff : ∀ k : ℤ, 0 < k → k < L → (X k).val ∉ chainVerts (Subtype.val ∘ γ) univ := by
    rintro k h0 h1 ⟨m, -, e | e⟩
    · exact hXu k h0 h1 (by rw [Subtype.ext e]; exact hγu m)
    · exact hXu k h0 h1 (by rw [Subtype.ext e]; exact hγu (m + 1))
  rw [Set.disjoint_left]
  intro v hv hvD
  simp only [arcTrace, chainTrace, mem_iUnion] at hv
  obtain ⟨k, ⟨h0, h1⟩, hv⟩ := hv
  have hadj := hX.adj_val k ⟨h0, h1⟩
  rcases h0.lt_or_eq with h0 | rfl
  · rw [edgeSegment_comm] at hv
    have := latticePoint_mem_connectedComponentIn hγ hadj.symm (hoff k h0 (by omega)) hv hvD
    exact hXu k h0 (by omega) (hD _ this)
  · have := latticePoint_mem_connectedComponentIn hγ hadj (hoff 1 one_pos (by omega)) hv hvD
    exact hXu 1 one_pos (by omega) (hD _ this)

theorem endpoints_mem_arcTrace (X : ℤ → C) {L : ℕ} (hL : 0 < L) :
    latticePoint (X 0).val ∈ arcTrace X L ∧ latticePoint (X L).val ∈ arcTrace X L := by
  constructor
  · exact mem_biUnion (x := 0) (show (0 : ℤ) ∈ Ico 0 (L : ℤ) from ⟨le_rfl, by omega⟩)
      (left_mem_edgeSegment _ _)
  · refine mem_biUnion (x := (L : ℤ) - 1)
      (show (L : ℤ) - 1 ∈ Ico 0 (L : ℤ) from ⟨by omega, by omega⟩) ?_
    simpa using right_mem_edgeSegment (X (L - 1)).val (X L).val

/-- The edges of `γ` indexed away from `[lo, hi]` miss an arc whose vertices on `γ` have their
index in `[lo, hi]`. -/
theorem disjoint_ray_arcTrace {γ : ℤ → C} (hγa : ∀ n, (componentGraph C).Adj (γ n) (γ (n + 1)))
    {F : Set ℤ} {lo hi : ℤ} (hF : ∀ m ∈ F, m + 1 < lo ∨ hi < m) {X : ℤ → C} {L : ℕ}
    (hX : IsSimpleChain (componentGraph C) X L)
    (hgood : ∀ k : ℤ, 0 ≤ k → k ≤ L → ∀ m, X k = γ m → lo ≤ m ∧ m ≤ hi) :
    Disjoint (chainTrace (Subtype.val ∘ γ) F) (arcTrace X L) := by
  refine disjoint_chainTrace (fun n _ => adj_val (hγa n)) hX.adj_val
    (Set.disjoint_left.2 fun z hz hz' => ?_)
  obtain ⟨k, hk0, hk1, rfl⟩ := exists_of_mem_chainVerts hz'
  obtain ⟨m, hm, e | e⟩ := hz
  · have := hgood k hk0 hk1 m (Subtype.ext e)
    have := hF m hm
    omega
  · have := hgood k hk0 hk1 (m + 1) (Subtype.ext e)
    have := hF m hm
    omega

theorem JordanSides.disjoint_outside {J I O : Set Plane} (h : JordanSides J I O) :
    Disjoint O J :=
  Set.disjoint_left.2 fun _ hvO hvJ => (show _ ∈ Jᶜ from h.union_eq ▸ Or.inr hvO) hvJ

/-- A preconnected set off `J` with a point outside lies outside. -/
theorem JordanSides.subset_outside_of_mem {J I O S : Set Plane} (h : JordanSides J I O)
    (hS : IsPreconnected S) (hSJ : Disjoint S J) {x : Plane} (hx : x ∈ S) (hxO : x ∈ O) :
    S ⊆ O := by
  refine hS.subset_left_of_subset_union h.isOpen_outside h.isOpen_inside h.disjoint.symm ?_
    ⟨x, hx, hxO⟩
  rw [union_comm, h.union_eq]
  exact fun _ hy hyJ => hSJ.ne_of_mem hy hyJ rfl

/-- A preconnected unbounded set off `J` lies outside. -/
theorem JordanSides.subset_outside_of_unbounded {J I O S : Set Plane} (h : JordanSides J I O)
    (hS : IsPreconnected S) (hSJ : Disjoint S J) (hb : ¬ Bornology.IsBounded S) : S ⊆ O :=
  h.subset_outside S (fun _ hy hyJ => hSJ.ne_of_mem hy hyJ rfl) hS (infty_mem_closure_image hb)

/-- Half-balls at a non-lattice point of an arc trace inside a union of lattice segments. -/
theorem exists_halfBalls_of_arcTrace {Θ : Set Plane} (hΘ : Θ ⊆ latticeSkeleton) {X : ℤ → C}
    {L : ℕ} (hX : IsSimpleChain (componentGraph C) X L) (hXΘ : arcTrace X L ⊆ Θ) {v : Plane}
    (hv : v ∈ arcTrace X L) (hvl : v ∉ range latticePoint) :
    ∃ δ > 0, ∃ H₁ H₂ : Set Plane, IsPreconnected H₁ ∧ IsPreconnected H₂ ∧ H₁.Nonempty ∧
      H₂.Nonempty ∧ Disjoint H₁ Θ ∧ Disjoint H₂ Θ ∧ Metric.ball v δ ⊆ H₁ ∪ H₂ ∪ Θ := by
  have hv' := hv
  simp only [arcTrace, chainTrace, mem_iUnion] at hv'
  obtain ⟨k, hk, hvk⟩ := hv'
  obtain ⟨δ, hδ, H₁, H₂, h₁, h₂, n₁, n₂, d₁, d₂, hball⟩ := exists_halfBalls (hX.adj_val k hk) hvk hvl
  have hseg : edgeSegment ((Subtype.val ∘ X) k) ((Subtype.val ∘ X) (k + 1)) ⊆ Θ :=
    fun w hw => hXΘ (mem_biUnion hk hw)
  exact ⟨δ, hδ, H₁, H₂, h₁, h₂, n₁, n₂, d₁.mono_right hΘ, d₂.mono_right hΘ,
    hball.trans (union_subset_union_right _ hseg)⟩

/-! ### The separation step -/

/-- step:5.19-jordan (L2051-2089): two zero stretches `σ`, `σ'` from `γ a`, `γ b`, whose last
vertices have neighbours `p, n` and `p', n'` joined in `{u > 0} \ Q_R` and `{u < 0} \ Q_R`, with
`p` and `n` joined to `Q_R` in `{u > 0}` and `{u < 0}`, are impossible. -/
theorem separationStep : SeparationStep := by
  intro hJ ω C u γ hγi hγa hγu z hz hD R c hc a b hab r r' σ σ' hσ hσ' hσ0 hσ'0 hσγ hσ'γ hσσ'
    hσu hσ'u p n p' n' hp hn hp' hn' hpp hnn ⟨yp, hyp, hpy⟩ ⟨yn, hyn, hny⟩
  have hPQ : σ r ≠ σ' r' := hσσ' r le_rfl r' le_rfl
  have hP0 : u (σ r) = 0 := (hσu r le_rfl).1
  have hQ0 : u (σ' r') = 0 := (hσ'u r' le_rfl).1
  have hab' : a ≠ b := fun h => hσσ' 0 (Nat.zero_le _) 0 (Nat.zero_le _) (by rw [hσ0, hσ'0, h])
  have hcab : c < min a b ∨ max a b < c := by
    by_contra h
    push Not at h
    exact hab c h.1 h.2 hc
  -- the vertices of the zero stretches on `γ` are `γ a` and `γ b`
  have hσgood : ∀ i ≤ r, ∀ m, σ i = γ m → min a b ≤ m ∧ m ≤ max a b := by
    intro i hi m e
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have := hγi (hσ0.symm.trans e)
      subst this
      exact ⟨min_le_left _ _, le_max_left _ _⟩
    · exact absurd ⟨m, e.symm⟩ (hσγ i hi0 hi)
  have hσ'good : ∀ i ≤ r', ∀ m, σ' i = γ m → min a b ≤ m ∧ m ≤ max a b := by
    intro i hi m e
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have := hγi (hσ'0.symm.trans e)
      subst this
      exact ⟨min_le_right _ _, le_max_right _ _⟩
    · exact absurd ⟨m, e.symm⟩ (hσ'γ i hi0 hi)
  -- simple chains
  obtain ⟨fp, ℓp, hfp0, hfp1, hfp, hfpS⟩ := exists_isSimpleChain_of_joinedIn hpp
  obtain ⟨fn, ℓn, hfn0, hfn1, hfn, hfnS⟩ := exists_isSimpleChain_of_joinedIn hnn
  obtain ⟨gp, mp, hgp0, hgp1, hgp, hgpS⟩ := exists_isSimpleChain_of_joinedIn hpy
  obtain ⟨gn, mn, hgn0, hgn1, hgn, hgnS⟩ := exists_isSimpleChain_of_joinedIn hny
  obtain ⟨τ, s, hτ0, hτ1, hτ, hτS⟩ := exists_isSimpleChain_of_joinedIn (joinedIn_of_chain σ r hσ)
  obtain ⟨τ', s', hτ'0, hτ'1, hτ', hτ'S⟩ :=
    exists_isSimpleChain_of_joinedIn (joinedIn_of_chain σ' r' hσ')
  -- the arcs `A_p` and `A_n`
  set Ap := chainBracket (σ r) fp ℓp (σ' r') with hAp
  set An := chainBracket (σ r) fn ℓn (σ' r') with hAn
  have hAp0 : Ap 0 = σ r := chainBracket_zero _ _ _ _
  have hApL : Ap ((ℓp + 2 : ℕ) : ℤ) = σ' r' := chainBracket_last _ _ _ _
  have hAn0 : An 0 = σ r := chainBracket_zero _ _ _ _
  have hAnL : An ((ℓn + 2 : ℕ) : ℤ) = σ' r' := chainBracket_last _ _ _ _
  have hApc : IsSimpleChain (componentGraph C) Ap (ℓp + 2) :=
    hfp.bracket (by rw [hfp0]; exact hp) (by rw [hfp1]; exact hp'.symm) hPQ
      (fun j _ _ h => by have := (hfpS j).1; rw [h, hP0] at this; exact lt_irrefl _ this)
      (fun j _ _ h => by have := (hfpS j).1; rw [h, hQ0] at this; exact lt_irrefl _ this)
  have hAnc : IsSimpleChain (componentGraph C) An (ℓn + 2) :=
    hfn.bracket (by rw [hfn0]; exact hn) (by rw [hfn1]; exact hn'.symm) hPQ
      (fun j _ _ h => by have := (hfnS j).1; rw [h, hP0] at this; exact lt_irrefl _ this)
      (fun j _ _ h => by have := (hfnS j).1; rw [h, hQ0] at this; exact lt_irrefl _ this)
  have hApu : ∀ k : ℤ, 0 ≤ k → k ≤ ((ℓp + 2 : ℕ) : ℤ) → 0 ≤ u (Ap k) := by
    intro k h0 h1
    rcases chainBracket_cases (σ r) fp ℓp (σ' r') h0 h1 with e | e | ⟨j, -, -, e⟩ <;>
      rw [hAp, e]
    · exact hP0.ge
    · exact hQ0.ge
    · exact (hfpS j).1.le
  have hAnu : ∀ k : ℤ, 0 ≤ k → k ≤ ((ℓn + 2 : ℕ) : ℤ) → u (An k) ≤ 0 := by
    intro k h0 h1
    rcases chainBracket_cases (σ r) fn ℓn (σ' r') h0 h1 with e | e | ⟨j, -, -, e⟩ <;>
      rw [hAn, e]
    · exact hP0.le
    · exact hQ0.le
    · exact (hfnS j).1.le
  have hApi : ∀ k : ℤ, 0 < k → k < ((ℓp + 2 : ℕ) : ℤ) → u (Ap k) ≠ 0 := by
    intro k h0 h1
    push_cast at h1
    rw [hAp, chainBracket_mid _ _ _ _ h0 (by omega)]
    exact (hfpS _).1.ne'
  have hAni : ∀ k : ℤ, 0 < k → k < ((ℓn + 2 : ℕ) : ℤ) → u (An k) ≠ 0 := by
    intro k h0 h1
    push_cast at h1
    rw [hAn, chainBracket_mid _ _ _ _ h0 (by omega)]
    exact (hfnS _).1.ne
  have hbr : ∀ (f : ℤ → C) (ℓ : ℕ), (∀ j, (f j).val ∉ cube R ∧ u (f j) ≠ 0) →
      ∀ k : ℤ, 0 ≤ k → k ≤ ((ℓ + 2 : ℕ) : ℤ) →
        (chainBracket (σ r) f ℓ (σ' r') k).val ∉ cube R ∧
        ∀ m, chainBracket (σ r) f ℓ (σ' r') k = γ m → min a b ≤ m ∧ m ≤ max a b := by
    intro f ℓ hf k h0 h1
    rcases chainBracket_cases (σ r) f ℓ (σ' r') h0 h1 with e | e | ⟨j, -, -, e⟩ <;> rw [e]
    · exact ⟨(hσu r le_rfl).2, hσgood r le_rfl⟩
    · exact ⟨(hσ'u r' le_rfl).2, hσ'good r' le_rfl⟩
    · exact ⟨(hf j).1, fun m e' => absurd (show u (f j) = 0 by rw [e', hγu]) (hf j).2⟩
  have hApg := hbr fp ℓp fun j => ⟨(hfpS j).2, (hfpS j).1.ne'⟩
  have hAng := hbr fn ℓn fun j => ⟨(hfnS j).2, (hfnS j).1.ne⟩
  -- the arc `A_z`: back along `σ`, along `γ` from `a` to `b`, out along `σ'`
  set ε : ℤ := if a ≤ b then 1 else -1 with hε
  set d : ℕ := if a ≤ b then (b - a).toNat else (a - b).toNat with hd
  have hεcase : (ε = 1 ∧ (d : ℤ) = b - a ∧ min a b = a ∧ max a b = b) ∨
      (ε = -1 ∧ (d : ℤ) = a - b ∧ min a b = b ∧ max a b = a) := by
    by_cases hle : a ≤ b
    · refine Or.inl ⟨if_pos hle, ?_, min_eq_left hle, max_eq_right hle⟩
      rw [hd, if_pos hle]
      omega
    · have hlt := (not_le.1 hle).le
      refine Or.inr ⟨if_neg hle, ?_, min_eq_right hlt, max_eq_left hlt⟩
      rw [hd, if_neg hle]
      omega
  have hd1 : 1 ≤ d := by rcases hεcase with ⟨-, e2, -⟩ | ⟨-, e2, -⟩ <;> omega
  have hεd : a + ε * d = b := by
    rcases hεcase with ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩ <;> rw [e1, e2] <;> ring
  have hεinj : ∀ j j' : ℤ, a + ε * j = a + ε * j' → j = j' := by
    intro j j' e
    rcases hεcase with ⟨e1, -⟩ | ⟨e1, -⟩ <;> rw [e1] at e <;> omega
  have hεm : ∀ j : ℤ, 0 ≤ j → j ≤ d → min a b ≤ a + ε * j ∧ a + ε * j ≤ max a b := by
    intro j h0 h1
    rcases hεcase with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ <;> rw [e1, e3, e4] <;> omega
  set gz : ℤ → C := fun j => γ (a + ε * j) with hgz
  have hgzc : IsSimpleChain (componentGraph C) gz d := by
    refine ⟨fun k _ _ => ?_, fun k k' _ _ _ _ e => hεinj _ _ (hγi e)⟩
    show (componentGraph C).Adj (γ (a + ε * k)) (γ (a + ε * (k + 1)))
    rcases hεcase with ⟨e1, -⟩ | ⟨e1, -⟩ <;> rw [e1]
    · rw [one_mul, one_mul, ← add_assoc]
      exact hγa _
    · have := (hγa (a + -1 * (k + 1))).symm
      rwa [show a + -1 * (k + 1) + 1 = a + -1 * k by ring] at this
  have hgz0 : gz 0 = σ 0 := by
    show γ (a + ε * 0) = σ 0
    rw [mul_zero, add_zero, hσ0]
  have hgzd : gz d = τ' 0 := by
    show γ (a + ε * d) = τ' 0
    rw [hεd, hτ'0, hσ'0]
  have hgzτ' : ∀ k k' : ℤ, 0 ≤ k → k ≤ d → 0 ≤ k' → k' ≤ s' → gz k = τ' k' →
      k = d ∧ k' = 0 := by
    intro k k' h0 h1 h0' h1' e
    obtain ⟨i, hi, hiτ⟩ := hτ'S k'
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have hk' : k' = 0 := hτ'.inj _ _ h0' h1' le_rfl (by omega) (by rw [← hiτ, hτ'0])
      have hk : a + ε * k = a + ε * d := hγi ((e.trans (hiτ.symm.trans hσ'0)).trans
        (congrArg γ hεd.symm))
      exact ⟨hεinj _ _ hk, hk'⟩
    · exact absurd ⟨a + ε * k, e.trans hiτ.symm⟩ (hσ'γ i hi0 hi)
  set Z := chainAppend gz d τ' with hZ
  have hZc : IsSimpleChain (componentGraph C) Z (d + s') := hgzc.append hτ' hgzd hgzτ'
  have hτZ : chainRev τ s s = Z 0 := by
    show τ ((s : ℤ) - s) = chainAppend gz d τ' 0
    rw [sub_self, chainAppend_of_le (by omega), hτ0, hgz0]
  have hτZd : ∀ k k' : ℤ, 0 ≤ k → k ≤ s → 0 ≤ k' → k' ≤ ((d + s' : ℕ) : ℤ) →
      chainRev τ s k = Z k' → k = s ∧ k' = 0 := by
    intro k k' h0 h1 h0' h1' e
    obtain ⟨i, hi, hiτ⟩ := hτS (s - k)
    by_cases hk' : k' ≤ d
    · rw [hZ, chainAppend_of_le hk'] at e
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · have hk : (s : ℤ) - k = 0 :=
          hτ.inj _ _ (by omega) (by omega) le_rfl (by omega) (by rw [← hiτ, hτ0])
        have : a + ε * 0 = a + ε * k' := by
          rw [mul_zero, add_zero]
          exact hγi (hσ0.symm.trans (hiτ.trans e))
        exact ⟨by omega, (hεinj _ _ this).symm⟩
      · exact absurd ⟨a + ε * k', (hiτ.trans e).symm⟩ (hσγ i hi0 hi)
    · rw [hZ, chainAppend_of_ge hgzd (by omega)] at e
      obtain ⟨i', hi', hiτ'⟩ := hτ'S (k' - d)
      exact absurd (hiτ.trans (e.trans hiτ'.symm)) (hσσ' i hi i' hi')
  set Az := chainAppend (chainRev τ s) s Z with hAz
  have hAzc : IsSimpleChain (componentGraph C) Az (s + (d + s')) := hτ.rev.append hZc hτZ hτZd
  have hAz0 : Az 0 = σ r := by
    rw [hAz, chainAppend_of_le (by omega)]
    show τ ((s : ℤ) - 0) = σ r
    rw [sub_zero, hτ1]
  have hAzL : Az ((s + (d + s') : ℕ) : ℤ) = σ' r' := by
    rw [hAz, chainAppend_of_ge hτZ (by push_cast; omega), hZ,
      chainAppend_of_ge hgzd (by push_cast; omega)]
    push_cast
    rw [show (s : ℤ) + (d + s') - s - d = s' by ring, hτ'1]
  have hAzs : Az s = γ a := by
    rw [hAz, chainAppend_of_le le_rfl]
    show τ ((s : ℤ) - s) = γ a
    rw [sub_self, hτ0, hσ0]
  have hAzs1 : Az (s + 1) = γ (a + ε) := by
    rw [hAz, chainAppend_of_ge hτZ (by omega), hZ, chainAppend_of_le (by omega)]
    show γ (a + ε * ((s : ℤ) + 1 - s)) = γ (a + ε)
    congr 1
    ring
  have hAzu : ∀ k : ℤ, 0 ≤ k → k ≤ ((s + (d + s') : ℕ) : ℤ) → u (Az k) = 0 ∧
      (Az k).val ∉ cube R ∧ ∀ m, Az k = γ m → min a b ≤ m ∧ m ≤ max a b := by
    intro k h0 h1
    rcases chainAppend_mem hτZ h0 (by push_cast at h1; exact h1) with
      ⟨j, hj0, hj1, e⟩ | ⟨j, hj0, hj1, e⟩
    · obtain ⟨i, hi, hiτ⟩ := hτS (s - j)
      rw [hAz, e, ← show σ i = chainRev τ s j from hiτ]
      exact ⟨(hσu i hi).1, (hσu i hi).2, hσgood i hi⟩
    · rcases chainAppend_mem hgzd hj0 (by push_cast at hj1; exact hj1) with
        ⟨j', hj0', hj1', e'⟩ | ⟨j', hj0', hj1', e'⟩
      · rw [hAz, e, hZ, e']
        refine ⟨hγu _, hab _ (hεm j' hj0' hj1').1 (hεm j' hj0' hj1').2, fun m e'' => ?_⟩
        rw [← hγi e'']
        exact hεm j' hj0' hj1'
      · obtain ⟨i, hi, hiτ⟩ := hτ'S j'
        rw [hAz, e, hZ, e', ← hiτ]
        exact ⟨(hσ'u i hi).1, (hσ'u i hi).2, hσ'good i hi⟩
  -- theta conditions and Jordan curves
  have thpz := theta_of_bracket (x := σ r) (y := σ' r') (f := fp) (ℓ := ℓp) hAzc hAz0 hAzL
    (fun j k' _ _ h0' h1' e => by
      have := (hfpS j).1
      rw [e, (hAzu k' h0' h1').1] at this
      exact lt_irrefl _ this)
  have thnz := theta_of_bracket (x := σ r) (y := σ' r') (f := fn) (ℓ := ℓn) hAzc hAz0 hAzL
    (fun j k' _ _ h0' h1' e => by
      have := (hfnS j).1
      rw [e, (hAzu k' h0' h1').1] at this
      exact lt_irrefl _ this)
  have thpn := theta_of_bracket (x := σ r) (y := σ' r') (f := fp) (ℓ := ℓp) hAnc hAn0 hAnL
    (fun j k' _ _ h0' h1' e => by
      have := (hfpS j).1
      rw [e] at this
      exact absurd (hAnu k' h0' h1') (not_le.2 this))
  obtain ⟨I₁, O₁, h₁⟩ := exists_jordanSides_of_arcs hJ hAnc hAzc (hAn0.trans hAz0.symm)
    (hAnL.trans hAzL.symm) (by omega) thnz
  obtain ⟨I₂, O₂, h₂⟩ := exists_jordanSides_of_arcs hJ hApc hAzc (hAp0.trans hAz0.symm)
    (hApL.trans hAzL.symm) (by omega) thpz
  obtain ⟨I₃, O₃, h₃⟩ := exists_jordanSides_of_arcs hJ hApc hAnc (hAp0.trans hAn0.symm)
    (hApL.trans hAnL.symm) (by omega) thpn
  set Kp := arcTrace Ap (ℓp + 2) with hKp
  set Kn := arcTrace An (ℓn + 2) with hKn
  set Kz := arcTrace Az (s + (d + s')) with hKz
  -- the three traces meet only at `P` and `Q`
  have iPN : Kp ∩ Kn ⊆ {latticePoint (σ r).val, latticePoint (σ' r').val} := by
    have := arcTrace_inter_subset hApc hAnc (by omega) thpn
    rwa [hAp0, hApL] at this
  have iPZ : Kp ∩ Kz ⊆ {latticePoint (σ r).val, latticePoint (σ' r').val} := by
    have := arcTrace_inter_subset hApc hAzc (by omega) thpz
    rwa [hAp0, hApL] at this
  have iNZ : Kn ∩ Kz ⊆ {latticePoint (σ r).val, latticePoint (σ' r').val} := by
    have := arcTrace_inter_subset hAnc hAzc (by omega) thnz
    rwa [hAn0, hAnL] at this
  set A₁ := arcInterior Ap (ℓp + 2) with hA₁
  set A₂ := arcInterior An (ℓn + 2) with hA₂
  set A₃ := arcInterior Az (s + (d + s')) with hA₃
  have dA₁ : Disjoint A₁ (Kn ∪ Kz) := disjoint_arcInterior hApc (by
    rw [hAp0, hApL]
    rintro v ⟨hv, hv' | hv'⟩
    · exact iPN ⟨hv, hv'⟩
    · exact iPZ ⟨hv, hv'⟩)
  have dA₂ : Disjoint A₂ (Kp ∪ Kz) := disjoint_arcInterior hAnc (by
    rw [hAn0, hAnL]
    rintro v ⟨hv, hv' | hv'⟩
    · exact iPN ⟨hv', hv⟩
    · exact iNZ ⟨hv, hv'⟩)
  have dA₃ : Disjoint A₃ (Kp ∪ Kn) := disjoint_arcInterior hAzc (by
    rw [hAz0, hAzL]
    rintro v ⟨hv, hv' | hv'⟩
    · exact iPZ ⟨hv', hv⟩
    · exact iNZ ⟨hv', hv⟩)
  have eP := endpoints_mem_arcTrace Ap (L := ℓp + 2) (by omega)
  have eN := endpoints_mem_arcTrace An (L := ℓn + 2) (by omega)
  rw [hAp0, hApL] at eP
  rw [hAn0, hAnL] at eN
  have hK₁ : Kp ⊆ A₁ ∪ (Kn ∪ Kz) := by
    intro v hv
    rcases arcTrace_subset Ap (L := ℓp + 2) (by omega) hv with h | h
    · exact Or.inl h
    · rw [hAp0, hApL] at h
      rcases h with rfl | rfl
      · exact Or.inr (Or.inl eN.1)
      · exact Or.inr (Or.inl eN.2)
  have hK₂ : Kn ⊆ A₂ ∪ (Kp ∪ Kz) := by
    intro v hv
    rcases arcTrace_subset An (L := ℓn + 2) (by omega) hv with h | h
    · exact Or.inl h
    · rw [hAn0, hAnL] at h
      rcases h with rfl | rfl
      · exact Or.inr (Or.inl eP.1)
      · exact Or.inr (Or.inl eP.2)
  have hK₃ : Kz ⊆ A₃ ∪ (Kp ∪ Kn) := by
    intro v hv
    rcases arcTrace_subset Az (L := s + (d + s')) (by omega) hv with h | h
    · exact Or.inl h
    · rw [hAz0, hAzL] at h
      rcases h with rfl | rfl
      · exact Or.inr (Or.inl eP.1)
      · exact Or.inr (Or.inl eP.2)
  -- the square `[-R, R]²` and the ray of `γ` beyond `γ c` are outside the three curves
  obtain ⟨Ray, F, hRc, hwR, hRb, hRT, hF⟩ := exists_ray hγi hcab
  have hwc : latticePoint (γ c).val ∈ realCube R := latticePoint_mem_realCube hc
  have hS₀c : IsPreconnected (realCube R ∪ Ray) :=
    (convex_realCube R).isPreconnected.union _ hwc hwR hRc
  have hS₀b : ¬ Bornology.IsBounded (realCube R ∪ Ray) :=
    fun h => hRb (h.subset subset_union_right)
  have hS₀ : ∀ {X : ℤ → C} {L : ℕ}, IsSimpleChain (componentGraph C) X L →
      (∀ k : ℤ, 0 ≤ k → k ≤ L → (X k).val ∉ cube R ∧
        ∀ m, X k = γ m → min a b ≤ m ∧ m ≤ max a b) →
      Disjoint (realCube R ∪ Ray) (arcTrace X L) := by
    intro X L hX hXg
    exact Set.disjoint_union_left.2
      ⟨(disjoint_arcTrace_realCube hX fun k h0 h1 => (hXg k h0 h1).1).symm,
        (disjoint_ray_arcTrace hγa hF hX fun k h0 h1 => (hXg k h0 h1).2).mono_left hRT⟩
  have dS₀p : Disjoint (realCube R ∪ Ray) Kp := hS₀ hApc hApg
  have dS₀n : Disjoint (realCube R ∪ Ray) Kn := hS₀ hAnc hAng
  have dS₀z : Disjoint (realCube R ∪ Ray) Kz :=
    hS₀ hAzc fun k h0 h1 => ⟨(hAzu k h0 h1).2.1, (hAzu k h0 h1).2.2⟩
  have hO₁ : realCube R ∪ Ray ⊆ O₁ :=
    h₁.subset_outside_of_unbounded hS₀c (Set.disjoint_union_right.2 ⟨dS₀n, dS₀z⟩) hS₀b
  have hO₂ : realCube R ∪ Ray ⊆ O₂ :=
    h₂.subset_outside_of_unbounded hS₀c (Set.disjoint_union_right.2 ⟨dS₀p, dS₀z⟩) hS₀b
  have hO₃ : realCube R ∪ Ray ⊆ O₃ :=
    h₃.subset_outside_of_unbounded hS₀c (Set.disjoint_union_right.2 ⟨dS₀p, dS₀n⟩) hS₀b
  have hwΘ : latticePoint (γ c).val ∉ Kp ∪ Kn ∪ Kz := by
    rintro ((h | h) | h)
    · exact dS₀p.ne_of_mem (Or.inl hwc) h rfl
    · exact dS₀n.ne_of_mem (Or.inl hwc) h rfl
    · exact dS₀z.ne_of_mem (Or.inl hwc) h rfl
  -- `A_p` and `A_n` are outside: `p` and `n` are joined to `Q_R` in `{u > 0}` and `{u < 0}`
  have hsign : ∀ {g : ℤ → C} {m : ℕ} {y : C}, g m = y → y.val ∈ cube R →
      ∀ {J I O : Set Plane}, JordanSides J I O → (realCube R ∪ Ray ⊆ O) →
      Disjoint (arcTrace g m ∪ {latticePoint y.val}) J → latticePoint (g 0).val ∈ O := by
    intro g m y hgm hy J I O h hO hd
    have himg : polyline (latticePoint ∘ (Subtype.val ∘ g)) '' Icc 0 (m : ℝ) ⊆
        arcTrace g m ∪ {latticePoint y.val} := by
      have := polyline_image_Icc_subset (Subtype.val ∘ g) m
      rw [Function.comp_apply, hgm] at this
      exact this
    have hym : latticePoint y.val ∈
        polyline (latticePoint ∘ (Subtype.val ∘ g)) '' Icc 0 (m : ℝ) := by
      refine ⟨m, ⟨by positivity, le_rfl⟩, ?_⟩
      have := polyline_intCast (latticePoint ∘ (Subtype.val ∘ g)) m
      push_cast at this
      rw [this]
      simp [hgm]
    have hpre : IsPreconnected
        (polyline (latticePoint ∘ (Subtype.val ∘ g)) '' Icc 0 (m : ℝ) ∪ (realCube R ∪ Ray)) :=
      (isPreconnected_Icc.image _ (continuous_polyline _).continuousOn).union _ hym
        (Or.inl (latticePoint_mem_realCube hy)) hS₀c
    have hsub := h.subset_outside_of_unbounded hpre
      (Set.disjoint_union_left.2 ⟨hd.mono_left himg, h.disjoint_outside.mono_left hO⟩)
      (fun hb => hS₀b (hb.subset subset_union_right))
    refine hsub (Or.inl ⟨0, ⟨le_rfl, by positivity⟩, ?_⟩)
    have := polyline_intCast (latticePoint ∘ (Subtype.val ∘ g)) 0
    push_cast at this
    exact this
  have hyp0 : 0 < u yp := hgp1 ▸ hgpS mp
  have hyn0 : u yn < 0 := hgn1 ▸ hgnS mn
  have hpO : latticePoint p.val ∈ O₁ := by
    have := hsign hgp1 hyp h₁ hO₁ (Set.disjoint_union_left.2
      ⟨Set.disjoint_union_right.2
        ⟨disjoint_arcTrace hgp hAnc fun k k' _ _ h0' h1' e => by
          have := hgpS k
          rw [mem_setOf_eq, e] at this
          exact absurd (hAnu k' h0' h1') (not_le.2 this),
        disjoint_arcTrace hgp hAzc fun k k' _ _ h0' h1' e => by
          have := hgpS k
          rw [mem_setOf_eq, e, (hAzu k' h0' h1').1] at this
          exact lt_irrefl _ this⟩,
      Set.disjoint_singleton_left.2 fun h => h.elim
        (latticePoint_not_mem_arcTrace hAnc fun k' h0' h1' e => by
          rw [e] at hyp0
          exact absurd (hAnu k' h0' h1') (not_le.2 hyp0))
        (latticePoint_not_mem_arcTrace hAzc fun k' h0' h1' e => by
          rw [e, (hAzu k' h0' h1').1] at hyp0
          exact lt_irrefl _ hyp0)⟩)
    rwa [hgp0] at this
  have hnO : latticePoint n.val ∈ O₂ := by
    have := hsign hgn1 hyn h₂ hO₂ (Set.disjoint_union_left.2
      ⟨Set.disjoint_union_right.2
        ⟨disjoint_arcTrace hgn hApc fun k k' _ _ h0' h1' e => by
          have := hgnS k
          rw [mem_setOf_eq, e] at this
          exact absurd (hApu k' h0' h1') (not_le.2 this),
        disjoint_arcTrace hgn hAzc fun k k' _ _ h0' h1' e => by
          have := hgnS k
          rw [mem_setOf_eq, e, (hAzu k' h0' h1').1] at this
          exact lt_irrefl _ this⟩,
      Set.disjoint_singleton_left.2 fun h => h.elim
        (latticePoint_not_mem_arcTrace hApc fun k' h0' h1' e => by
          rw [e] at hyn0
          exact absurd (hApu k' h0' h1') (not_le.2 hyn0))
        (latticePoint_not_mem_arcTrace hAzc fun k' h0' h1' e => by
          rw [e, (hAzu k' h0' h1').1] at hyn0
          exact lt_irrefl _ hyn0)⟩)
    rwa [hgn0] at this
  have hAp1 : Ap 1 = p := by
    rw [hAp, chainBracket_mid _ _ _ _ one_pos (by omega), sub_self, hfp0]
  have hAn1 : An 1 = n := by
    rw [hAn, chainBracket_mid _ _ _ _ one_pos (by omega), sub_self, hfn0]
  have hpA : latticePoint p.val ∈ A₁ := by
    have := latticePoint_mem_arcInterior Ap (L := ℓp + 2) (k := 1) one_pos (by push_cast; omega)
    rwa [hAp1] at this
  have hnA : latticePoint n.val ∈ A₂ := by
    have := latticePoint_mem_arcInterior An (L := ℓn + 2) (k := 1) one_pos (by push_cast; omega)
    rwa [hAn1] at this
  have hA₁O : A₁ ⊆ O₁ :=
    h₁.subset_outside_of_mem (isPreconnected_arcInterior _ _) dA₁ hpA hpO
  have hA₂O : A₂ ⊆ O₂ :=
    h₂.subset_outside_of_mem (isPreconnected_arcInterior _ _) dA₂ hnA hnO
  -- `A_z` is outside `K_p ∪ K_n`: the side `D` of `γ` reaches the middle of its first `γ`-edge
  have hinjγ : Function.Injective (Subtype.val ∘ γ) := Subtype.val_injective.comp hγi
  obtain ⟨β, hβ, hβr⟩ := exists_path_line hinjγ fun m => adj_val (hγa m)
  rw [← pathTrace_eq_chainTrace] at hβr
  obtain ⟨hTD, hND⟩ := closure_connectedComponentIn_of_sphere hJ β hβ hβr hz
  have hDJ : Disjoint (connectedComponentIn (pathTrace γ)ᶜ z) (Kp ∪ Kn) :=
    Set.disjoint_union_right.2
      ⟨(disjoint_arcTrace_component hγu hγa hD hApc (by omega) hApi).symm,
        (disjoint_arcTrace_component hγu hγa hD hAnc (by omega) hAni).symm⟩
  have hDO : connectedComponentIn (pathTrace γ)ᶜ z ⊆ O₃ :=
    h₃.subset_outside _ (fun _ hy hyJ => hDJ.ne_of_mem hy hyJ rfl)
      isPreconnected_connectedComponentIn hND
  have hfl : ⌊(s : ℝ) + 1 / 2⌋ = s := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  set x := polyline (latticePoint ∘ (Subtype.val ∘ Az)) ((s : ℝ) + 1 / 2) with hx
  have hxA : x ∈ A₃ := by
    refine ⟨(s : ℝ) + 1 / 2, ⟨by positivity, ?_⟩, rfl⟩
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    push_cast
    linarith [(Nat.cast_nonneg s' : (0 : ℝ) ≤ s')]
  have hxe : x ∈ edgeSegment (γ a).val (γ (a + ε)).val := by
    have := polyline_mem_edgeSegment (Subtype.val ∘ Az) ((s : ℝ) + 1 / 2)
    rw [hfl] at this
    have e1 : (Subtype.val ∘ Az) (s : ℤ) = (γ a).val := by
      show (Az s).val = _
      rw [hAzs]
    have e2 : (Subtype.val ∘ Az) ((s : ℤ) + 1) = (γ (a + ε)).val := by
      show (Az (s + 1)).val = _
      rw [hAzs1]
    rw [e1, e2] at this
    exact this
  have hxT : x ∈ pathTrace γ := by
    rw [pathTrace_eq_chainTrace]
    rcases hεcase with ⟨e1, -⟩ | ⟨e1, -⟩ <;> rw [e1] at hxe
    · exact mem_biUnion (x := a) (mem_univ _) hxe
    · rw [edgeSegment_comm] at hxe
      refine mem_biUnion (x := a + -1) (mem_univ _) ?_
      simpa using hxe
  have hxO : x ∈ O₃ := by
    have hxJ : x ∈ (Kp ∪ Kn)ᶜ := fun h => dA₃.ne_of_mem hxA h rfl
    rw [← h₃.union_eq] at hxJ
    rcases hxJ with hxI | hxO
    · obtain ⟨y, hyI, hyD⟩ := mem_closure_iff.1 (hTD hxT) I₃ h₃.isOpen_inside hxI
      exact absurd (hDO hyD) (h₃.disjoint.ne_of_mem hyI · rfl)
    · exact hxO
  have hA₃O : A₃ ⊆ O₃ :=
    h₃.subset_outside_of_mem (isPreconnected_arcInterior _ _) dA₃ hxA hxO
  have hxl : x ∉ range latticePoint := by
    rintro ⟨z', hz'⟩
    have hadj := hAzc.adj_val ⌊(s : ℝ) + 1 / 2⌋ (by rw [hfl]; exact ⟨by omega, by omega⟩)
    obtain ⟨-, hf⟩ := polyline_eq_latticePoint hadj hz'.symm
    rw [Int.fract, hfl] at hf
    norm_num at hf
  -- the theta graph
  have hΘs : Kp ∪ Kn ∪ Kz ⊆ latticeSkeleton :=
    union_subset (union_subset (chainTrace_subset_latticeSkeleton hApc.adj_val)
      (chainTrace_subset_latticeSkeleton hAnc.adj_val))
      (chainTrace_subset_latticeSkeleton hAzc.adj_val)
  have hΘc : IsClosed (Kp ∪ Kn ∪ Kz) :=
    ((isClosed_chainTrace _ (finite_Ico _ _)).union (isClosed_chainTrace _ (finite_Ico _ _))).union
      (isClosed_chainTrace _ (finite_Ico _ _))
  refine false_of_theta hΘc ?_ h₁ h₂ h₃ hK₁ hA₁O (arcInterior_subset _ _) hK₂ hA₂O ⟨_, hnA⟩
    (arcInterior_subset _ _) hK₃ hA₃O ⟨x, hxA⟩ hwΘ (hO₁ (Or.inl hwc)) (hO₂ (Or.inl hwc))
    (hO₃ (Or.inl hwc)) ⟨x, Or.inr (arcInterior_subset _ _ hxA), hxl⟩
  rintro v ((hv | hv) | hv) hvl
  · exact exists_halfBalls_of_arcTrace hΘs hApc (subset_union_left.trans subset_union_left) hv hvl
  · exact exists_halfBalls_of_arcTrace hΘs hAnc (subset_union_right.trans subset_union_left) hv
      hvl
  · exact exists_halfBalls_of_arcTrace hΘs hAzc subset_union_right hv hvl

end Rigidity.Proofs.Section5
