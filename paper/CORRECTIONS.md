# Corrections in paper/percolation-harmonic-corrected.tex

Surgical corrections to arXiv:2303.04736v2, made with the approval of Ahmed Bou-Rabee, one of the
authors. The preserved source is paper/percolation-harmonic.tex (identical to the arXiv
source). The corrected draft is produced from it by paper/make_corrected.py; each change carries a
comment `% CORRECTION [Cn]` above the changed line that gives its reason in short, and the entries
below give the reason for each correction (sub-tags without an entry refer to the main tag). There are
60 tags, for 38 numbered corrections C1-C39 (there is no C27). Each correction
was tested in an independent model review, and the literature inputs C34 and C35 were checked
against their sources; paper/open-gadget-correction.tex explains C9 and C10. The Lean statements
follow the corrected draft. A correction applied at several places carries the tags Cn, Cnb, Cnc, ...

The entries name the gaps of the printed proofs that they repair as follows: G1, the mixing bound in
the proof of Theorem 6.5 (C33); G2, the conditional bound in the proof of Lemma 4.8 (C36); G3, the
passage from the chemical to the Euclidean distance in the proof of Lemma 3.1 (C26); G4, the
measurability and nonconstancy in the proof of Proposition 4.10 (C28); G5, the direction of the edge
in the event G_3 (C32); G6, the quantifier in the event G_1 (C31); G7, the general slope in the proof
of Proposition 5.11 (C30); G8, the lower limit in Proposition 5.11 (C29).

- [C1] T_L uses x_1 <= L (|x|_inf <= L): with the l^1 norm |T_L| ~ L^2/2 and Lemma lemma:density-bound-good-event would read P[G]/2; its proof uses this triangle.
- [C2] Euclidean norm in the continuum Green's function (|x| denotes the l^1 norm).
- [C2b] Euclidean norm in the continuum Green's function.
- [C3] with G(y,y) = 0 the constant at infinity depends on the pole (a leaf y' attached to y gives G(x,y') = G(x,y) - 1 for x != y'); Section 5 uses the normalized Green's function H.
- [C4] with the convention (id:vectorfiedledges) the printed left side is of order |grad Gbar| (e.g. at a leaf whose only neighbour is x + e_j); the orientation-consistent form uses grad of the corrected planes, which also vanishes on closed edges. In d = 2 the proof subtracts kappa(y) and the local logarithmic constant before the regularity estimates.
- [C5] sign: with the convention (id:vectorfiedledges), grad l_xi = -xi on open edges and 0 on closed edges.
- [C6] the bound holds for the normalized Green's function H; in d = 2 it fails for G at a leaf. Mixed derivatives of G and H coincide.
- [C7] as printed the lemma is false: two simple lattice rays from two corners of a square that merge into one ray leave a single component with N in its closure. The proof uses that the beta_i are Jordan curves.
- [C8] indexing: alpha_i runs from x_i to x_{i+1}; indices modulo K.
- [C9] paper/open-gadget-correction.tex: on the closed rectangle the claim is false (values at unused closed sites make u nonconstant without changing the terminals); it holds on the open carrier T^1_n with its induced graph.
- [C10] direction of divisibility (paper/open-gadget-correction.tex): u(a) = (B_n / A_{n+1}) u(t) is an integer and gcd(A_{n+1}, B_n) = 1.
- [C11] as printed the lemma is trivial (constants, slope 0); its proof and its use (lemma:det-slope needs a nonzero slope) take a non-constant function and give |p| >= 1 after rescaling.
- [C12] for u -> 0 the printed limsup |u(x)|/|x| is always 0 (and the theorem false as printed: a dipole of H across an edge where l_{e_1} varies); decay at most like |x|^{-1} is limsup |x| |u(x)| > 0.
- [C13] potential of the normalized Green's function H (see C3): with G, a leaf at a pole gives a mean-zero potential tending to a nonzero constant, and Props prop:gradient-trichotomy, prop:two-scale-expansion-mean-zero, prop:level-set-of-harmonic-function fail.
- [C14] the representation holds for any kernel; with H (see C13).
- [C15] the proof passed from a general u to u_f without justification; the identification u = u_f is added.
- [C16] for H (see C6); for G it fails in d = 2.
- [C17] p = 0 must be excluded (l_0 is constant; noncompact mean-zero potentials exist); the proof uses the ray R p.
- [C18] sign of the leading term: moving the pole to the source variable, grad Gbar is odd; the leading term is -sum_i M_i d_i Gbar(x).
- [C19] the slope p is fixed and nonzero (as in prop:gradient-trichotomy).
- [C20] barrier sign: G(., a) <= 0 tends to -infinity; the proof needs v >= 0 tending to +infinity.
- [C21] the condition is on a component D of R^2 \\ gamma, as used in the proof (C_inf cap D subset L_0).
- [C22] the connectors must join all K+2 initial points.
- [C23] distances from the starting point x, so that G_1(x, K) is the translate of G_1(0, K) (used in lemma:density-bound-good-event).
- [C24] printed '2 diam R''; read as twice the l^inf diameter 2R' of Q_{R'}(x).
- [C25] the multiplicative harmonic function equals -1 at two sites, so its eigenvalue is 1 - 4/m; the theorem is unchanged.
- [C26] Lipschitz is for the chemical distance; membership in A_1 needs a chemical-distance comparison (gap G3).
- [C27] not used: the printed Lemma lemma:non-constant-on-gadget (Lemma 4.8) is true, and Lean proves it as stated (Rigidity.Assembly.Main.nonConstantOnGadget). Its printed proof has gap G2, repaired by C36-C36g; C37-C37b repair the proof of Lemma 4.7 accordingly. No statement changes.
- [C36] gap G2: the averaging argument below resets only edges fixed by every event C_inf cap Q_R = H'; so the comparison environment keeps the edges leaving Q_R and the edges at the (d-2)-skeleton of Q_R random, and opens the faces F_R instead of closing the edges at the boundary of Q_R.
- [C36b] see C36.
- [C36c] see C36.
- [C36d] see C36; union bound over one face site, the other one fixed.
- [C36e] see C36.
- [C36f] see C36.
- [C36g] gap G2: conditioning on C_inf cap Q_R = H' reweights the edges the proof leaves free; averaging over H' after resetting a finite set D of edges fixed by every such event gives the conditional bound (Lean: Rigidity/Proofs/S4/OuterNonConstant/Reset.lean, exists_conditional_ge).
- [C37] the event C_inf cap Q_R = H depends on the edges outside Q_R, so its probability is not a product over the sites of Q_R; the proof of lemma:non-constant-on-gadget gives the lower bound, and the isolation of the gadget needed by prop:exponential-growth-gadget.
- [C37b] see C37.
- [C28] measurability of E, needed for the ergodic theorem (gap G4).
- [C28b] nonconstancy of v (gap G4).
- [C29] Step 3 of the proof of prop:gradient-trichotomy gives E[1_E N_k]/|B_{2^k}| -> 0, which by Fatou contradicts a positive lower limit but not a positive upper limit (typewriter sequence); the proof of this proposition (lemma:density-bound-good-event) gives the lower limit (gap G8).
- [C29b] see C29.
- [C30] the printed proof of prop:level-set-of-harmonic-function treats p = e_1 only (the counting uses grad l_{e_1}); the statement holds for every fixed p != 0 with these changes (gap G7).
- [C31] printed with an existential over gamma: then G_1(x, K) lies in {x in C_inf} and eq:PG1goesto1 fails (P <= theta(p) < 1), and Step 6 of lemma:large-gradient-implies-not-in-level-set applies G_1 to a given path; the complement of the universal event is the event of prop:longpathsupercritrenormlatt (gap G6).
- [C32] Alternative statement of Lemmas 5.25-5.27, not a correction of a false statement: the published Lemma 5.25 is also proved, as Rigidity.Assembly.Main.goodEventLowerBoundDirectional. Prop prop:not-lipschitz bounds |grad l_{e_1}(0)| without sign or direction, and the symmetries fixing the slope e_1 preserve the sign of l(x+e_1) - l(x), so the printed event (the edge (x, x+e_1)) is not shown to have positive probability; the proof of lemma:large-gradient-implies-not-in-level-set uses x + e_1 only as a neighbour of x (gap G5). The printed Lemma lemma:good-event-lower-bound (Lemma 5.25), with the printed event on the edge (x, x+e_1), is nevertheless TRUE: Lean proves it as Rigidity.Assembly.Main.goodEventLowerBoundDirectional (signed Prop 3.2 through the exterior network, Proofs/S3/ExteriorNetwork.lean). C32 is kept because the direction-free event gives the short repaired proof; it is not a correction of a false statement.
- [C32b] see C32 (alternative statement of Lemmas 5.25-5.27).
- [C32c] see C32 (alternative statement of Lemmas 5.25-5.27).
- [C32d] see C32 (alternative statement of Lemmas 5.25-5.27).
- [C32e] see C32.
- [C32f] see C32.
- [C33] Jerison-Levine-Pike, Theorem 4.3, concerns the chain with holding probability 1/(m+1) on a simple graph; for the chain defined above the cited bound fails when every site has an even number of exits (eigenvalue -1). The theorem holds with the single-exit argument (gap G1).
- [C33b] see C33.
- [C34] the proof of prop:homogenizationellipticgreen (eq. large scale-regularity) uses the local estimate of the cited theorem, part (iii) of Theorem 2 in arXiv:1609.09431v2, which the quotation omitted.
- [C35] Penrose-Pisztora 1996, Theorem 1, concerns continuum percolation, and their lattice results are for site percolation; the density estimate for bond percolation in every d >= 2 is Dario-Gu, Proposition A.1, with a union bound over the triadic cubes inside the balls.
- [C38] as printed the lemma is false for a constant loop (one component) or a figure-eight (three components); the Jordan curve theorem is for simple loops, and the two components are disjoint. The Lean input Rigidity.External.JordanCurveTheoremSphere is stated for simple loops.
- [C39] the domain lies in the plane R^2, as in the cited remark of Rudin; a subset of Z^2 is not a domain. No Lean proof uses this lemma.

## Where the Lean proof departs from the printed argument

At three places the Lean proofs do not follow the printed text of the corrected draft. The statements
are unchanged; the line numbers are those of paper/percolation-harmonic-corrected.tex.

1. Finiteness of the biconnected components of the exploration graph (L2515-2520, in the proof of
   Lemma 5.27; Lemma 5.28 concerns the block-cut tree of this graph). The text derives it from Proposition 5.20 and the preceding
   observation. The Lean proof of Lemma 5.28 does not use it: a branch of the block-cut tree that ends
   at an infinite leaf block contains an infinite path and is counted with the paths to infinity
   (Rigidity/Proofs/Section5/InfiniteBranches.lean, infiniteBranchesStep; assembled by
   finiteBranches_of_steps in Rigidity/Steps/Section5/FiniteBranches.lean). Step 2 of Lemma 5.27 does
   not use it either (Rigidity/Steps/Section5/LargeGradientSensitive.lean).
2. The constant C_chi of Lemma 5.27 (L2491-2495, L2659-2667, L2676). The Lean proof chooses its own
   window and constant, C_chi = max(1, 128 (2W + 1) exp(C_branches) / c_1) with W = ceil(4R^2), and
   counts the good points of a window by TerminationWindowStep
   (Rigidity/Steps/Section5/LargeGradientSensitive.lean; W and C_chi are set in
   largeGradientSensitive_of_steps, Rigidity/Steps/Section5/DirectionFree.lean). The statement asserts
   only that some C_chi exists.
3. Details of the proof of Proposition 3.2 (Steps 2 and 3, L980-988, L1031-1056, L1070-1086,
   L1098-1110). The Lean proof (Rigidity/Steps/S3/NotLipschitz.lean, notLipschitz_of_steps) bounds
   the outward flux through the edges (x, x - e_1), x in left(Q_N) (FluxEventStep, proved in
   Rigidity/Proofs/S3/FluxEvent.lean); replaces "Similarly" by a lattice sum of the Green kernel
   (GreenKernelSumStep); bounds the gradient across a bridge one side of which is finite
   (BridgeFluxStep); and bounds the short paths across the removed edges by C N^(1/2) and the other
   contributing edges of the centre face by C N^(d-1-1/(10d)+1/(10d)^2), in place of N^(d-1-1/2)
   (ShortPathsStep).
