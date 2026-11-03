import Rigidity.Steps.Section5.NoThickPaths

/-!
# Lemma 5.19: the signs around the zero stretches

This file proves `SignsStep` (`step:5.19-signs`, corrected draft L2045-2051). No literature input
is used.

Let `-Δu = f` with `supp f ⊆ Q_R`, every component of `{u > 0}` and of `{u < 0}` meeting a pole,
and let `ρ k` be more than `|Q_{R+1}|²` paths outside `Q_{R+1}` from a zero of `u` to a nonzero
value. For each `k`:

* `exists_last_zero`: the initial zero stretch `ρ k [0, r]` is followed by a nonzero value;
* `exists_pos_neg_of_harmonic`: `u` is harmonic at `z = ρ k r ∉ supp f` and vanishes there, so a
  neighbour with `u ≠ 0` forces neighbours `p`, `n` of `z` with `u(p) > 0 > u(n)`;
* the components of `{u > 0}` through `p` and of `{u < 0}` through `n` meet a pole `y ∈ Q_R`, and
  `exists_exit_of_joinedIn` gives the last vertex `a` (resp. `b`) before `Q_R` of a path from
  `p` (resp. `n`) to `y`: it lies in `Q_{R+1}` and is joined to `p` (resp. `n`) outside `Q_R`.

The pigeonhole principle on the pairs `(a, b) ∈ Q_{R+1} × Q_{R+1}` gives `k ≠ l` with the same
pair, hence `p_k`, `p_l` joined in `{u > 0} \ Q_R` and `n_k`, `n_l` joined in `{u < 0} \ Q_R`.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

variable {ω : Configuration 2}

/-- Adjacent vertices of `𝒞_∞` differ by at most one in each coordinate. -/
theorem abs_sub_le_one_of_adj {C : OpenComponent ω} {x y : C}
    (h : (componentGraph C).Adj x y) (i : Fin 2) : |x.val i - y.val i| ≤ 1 := by
  have h1 := lattice_adj_iff_l1Dist.1 ((C.toSimpleGraph_adj x.2 y.2).1 h).1
  simp only [latticeL1Dist, Fin.sum_univ_two] at h1
  have := abs_nonneg (x.val 0 - y.val 0)
  have := abs_nonneg (x.val 1 - y.val 1)
  fin_cases i <;> simp <;> linarith

/-- A neighbour of a vertex of `Q_R` lies in `Q_{R+1}`. -/
theorem mem_cube_succ_of_adj {C : OpenComponent ω} {x y : C} {R : ℕ}
    (h : (componentGraph C).Adj x y) (hy : y.val ∈ cube R) : x.val ∈ cube (R + 1) := by
  intro i
  have h1 := abs_le.1 (abs_sub_le_one_of_adj h i)
  have h2 := abs_le.1 (hy i)
  push_cast
  exact abs_le.2 ⟨by omega, by omega⟩

/-- Being joined inside `S` is transitive. -/
theorem joinedIn_trans {C : OpenComponent ω} {S : Set C} {x y z : C} (hxy : JoinedIn C S x y)
    (hyz : JoinedIn C S y z) : JoinedIn C S x z := by
  obtain ⟨hx, _, h1⟩ := hxy
  obtain ⟨_, hz, h2⟩ := hyz
  exact ⟨hx, hz, h1.trans h2⟩

/-- A path inside `S` from outside `Q` to `Q` leaves `S \ Q` at a vertex adjacent to `Q`. -/
theorem exists_exit_of_joinedIn {C : OpenComponent ω} {S Q : Set C} {x y : C}
    (hxy : JoinedIn C S x y) (hx : x ∉ Q) (hy : y ∈ Q) :
    ∃ a, JoinedIn C (S \ Q) x a ∧ ∃ b ∈ Q, (componentGraph C).Adj a b := by
  obtain ⟨_, _, ⟨w⟩⟩ := hxy
  suffices h : ∀ (x' y' : S) (w : ((componentGraph C).induce S).Walk x' y'), x'.val ∉ Q →
      y'.val ∈ Q → ∃ a, JoinedIn C (S \ Q) x'.val a ∧ ∃ b ∈ Q, (componentGraph C).Adj a b from
    h _ _ w hx hy
  intro x' y' w
  induction w with
  | nil => exact fun h1 h2 => absurd h2 h1
  | @cons a b c hab w ih =>
    intro h1 h2
    by_cases hb : b.val ∈ Q
    · exact ⟨a.val, ⟨⟨a.2, h1⟩, ⟨a.2, h1⟩, SimpleGraph.Reachable.refl _⟩, b.val, hb, hab⟩
    · obtain ⟨a', ⟨hb', ha', hr⟩, b', hb'Q, hadj⟩ := ih hb h2
      have hadj' : ((componentGraph C).induce (S \ Q)).Adj ⟨a.val, ⟨a.2, h1⟩⟩ ⟨b.val, hb'⟩ := hab
      exact ⟨a', ⟨⟨a.2, h1⟩, ha', hadj'.reachable.trans hr⟩, b', hb'Q, hadj⟩

/-- A sequence vanishing at `0` and nonzero at `ℓ` has an initial zero stretch `[0, r]`, `r < ℓ`,
followed by a nonzero value. -/
theorem exists_last_zero {g : ℕ → ℝ} {ℓ : ℕ} (h0 : g 0 = 0) (hℓ : g ℓ ≠ 0) :
    ∃ r < ℓ, (∀ i ≤ r, g i = 0) ∧ g (r + 1) ≠ 0 := by
  classical
  have hex : ∃ j, g j ≠ 0 := ⟨ℓ, hℓ⟩
  have hspec := Nat.find_spec hex
  have hle := Nat.find_min' hex hℓ
  have hpos : 0 < Nat.find hex := Nat.pos_of_ne_zero fun h => hspec (by rw [h]; exact h0)
  refine ⟨Nat.find hex - 1, by omega, fun i hi => ?_, by rwa [Nat.sub_add_cancel hpos]⟩
  by_contra hne
  exact Nat.find_min hex (by omega : i < Nat.find hex) hne

/-- At a zero `z` of `u` where `u` is harmonic, a neighbour where `u ≠ 0` forces neighbours of `z`
where `u > 0` and where `u < 0`. -/
theorem exists_pos_neg_of_harmonic {C : OpenComponent ω} {u : C → ℝ} {z w : C}
    (hz : componentLaplacian C u z = 0) (hz0 : u z = 0) (hzw : (componentGraph C).Adj z w)
    (hw : u w ≠ 0) :
    (∃ p, (componentGraph C).Adj z p ∧ 0 < u p) ∧ ∃ n, (componentGraph C).Adj z n ∧ u n < 0 := by
  have hsum : ∑ y ∈ (componentGraph C).neighborFinset z, u y = 0 := by
    simpa [componentLaplacian, hz0] using hz
  have hwmem : w ∈ (componentGraph C).neighborFinset z :=
    (SimpleGraph.mem_neighborFinset _ _ _).2 hzw
  constructor
  · by_contra hcon
    push Not at hcon
    exact hw ((Finset.sum_eq_zero_iff_of_nonpos fun y hy =>
      hcon y ((SimpleGraph.mem_neighborFinset _ _ _).1 hy)).1 hsum w hwmem)
  · by_contra hcon
    push Not at hcon
    exact hw ((Finset.sum_eq_zero_iff_of_nonneg fun y hy =>
      hcon y ((SimpleGraph.mem_neighborFinset _ _ _).1 hy)).1 hsum w hwmem)

/-- **Step `step:5.19-signs`** of Lemma 5.19: among more than `|Q_{R+1}|²` paths outside
`Q_{R+1}` from a zero of `u` to a nonzero value, two have zero stretches whose last vertices have
neighbours of both signs, joined pairwise outside `Q_R` within the sign classes, and joined to
`Q_R` (to a pole) within the sign classes. -/
theorem signsStep : SignsStep := by
  intro ω C f u hΔ hP hN R hRf N hN2 ℓ ρ hρa hρ0 hρu hρR
  have hset : {x : C | 0 < (-u) x} = {x | u x < 0} := Set.ext fun x => by simp
  have hN' : ∀ T, IsComponentOf C {x | u x < 0} T → ∃ y ∈ T, f y.val ≠ 0 := by
    rw [← hset]
    intro T hT
    obtain ⟨y, hy, hy'⟩ := hN T hT
    exact ⟨y, hy, by simpa using hy'⟩
  have key : ∀ k, ∃ r ≤ ℓ k, (∀ i ≤ r, u (ρ k i) = 0) ∧ ∃ p n : C,
      (componentGraph C).Adj (ρ k r) p ∧ (componentGraph C).Adj (ρ k r) n ∧
      (∃ y : C, y.val ∈ cube R ∧ JoinedIn C {x | 0 < u x} p y) ∧
      (∃ y : C, y.val ∈ cube R ∧ JoinedIn C {x | u x < 0} n y) ∧
      ∃ a b : C, a.val ∈ cube (R + 1) ∧ b.val ∈ cube (R + 1) ∧
        JoinedIn C {x | 0 < u x ∧ x.val ∉ cube R} p a ∧
        JoinedIn C {x | u x < 0 ∧ x.val ∉ cube R} n b := by
    intro k
    obtain ⟨r, hrℓ, hz, hnz⟩ :=
      exists_last_zero (g := fun i => u (ρ k i)) (hρ0 k) (hρu k)
    have hzR : (ρ k r).val ∉ cube (R + 1) := hρR k r hrℓ.le
    have hf : f (ρ k r).val = 0 := by
      by_contra h
      exact hzR (cube_mono (Nat.le_succ R) (hRf _ h))
    have hlap : componentLaplacian C u (ρ k r) = 0 := by
      have := hΔ (ρ k r)
      rw [hf] at this
      simpa using this
    obtain ⟨⟨p, hp, hup⟩, n, hn, hun⟩ :=
      exists_pos_neg_of_harmonic hlap (hz r le_rfl) (hρa k r hrℓ) hnz
    obtain ⟨y, hyT, hyf⟩ := hP {x | JoinedIn C {x | 0 < u x} p x} ⟨p, hup, rfl⟩
    obtain ⟨y', hyT', hyf'⟩ := hN' {x | JoinedIn C {x | u x < 0} n x} ⟨n, hun, rfl⟩
    have hyR : y.val ∈ cube R := hRf _ hyf
    have hyR' : y'.val ∈ cube R := hRf _ hyf'
    have hpR : p.val ∉ cube R := fun h => hzR (mem_cube_succ_of_adj hp h)
    have hnR : n.val ∉ cube R := fun h => hzR (mem_cube_succ_of_adj hn h)
    obtain ⟨a, ha, a1, ha1, haa⟩ :=
      exists_exit_of_joinedIn (Q := {x : C | x.val ∈ cube R}) hyT hpR hyR
    obtain ⟨b, hb, b1, hb1, hbb⟩ :=
      exists_exit_of_joinedIn (Q := {x : C | x.val ∈ cube R}) hyT' hnR hyR'
    exact ⟨r, hrℓ.le, hz, p, n, hp, hn, ⟨y, hyR, hyT⟩, ⟨y', hyR', hyT'⟩, a, b,
      mem_cube_succ_of_adj haa ha1, mem_cube_succ_of_adj hbb hb1, ha, hb⟩
  choose r hrℓ hz p n hp hn hpy hny a b ha hb hpa hnb using key
  obtain ⟨k, -, l, -, hkl, heq⟩ := Set.exists_ne_map_eq_of_ncard_lt_of_maps_to
    (s := Set.univ) (t := cube (R + 1) ×ˢ cube (R + 1)) (f := fun k => ((a k).val, (b k).val))
    (by rw [Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, ← sq]
        exact hN2)
    (fun k _ => ⟨ha k, hb k⟩) ((cube_finite _).prod (cube_finite _))
  simp only [Prod.mk.injEq] at heq
  have ha' : a k = a l := Subtype.ext heq.1
  have hb' : b k = b l := Subtype.ext heq.2
  refine ⟨k, l, hkl, r k, r l, hrℓ k, hrℓ l, hz k, hz l, p k, n k, p l, n l, hp k, hn k, hp l,
    hn l, joinedIn_trans (hpa k) ?_, joinedIn_trans (hnb k) ?_, hpy k, hny k⟩
  · rw [ha']
    exact joinedIn_symm (hpa l)
  · rw [hb']
    exact joinedIn_symm (hnb l)

end Rigidity.Proofs.Section5
