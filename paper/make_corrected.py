# Run from the repository root:
#   python3 paper/make_corrected.py paper/percolation-harmonic.tex paper/percolation-harmonic-corrected.tex
"""Build paper/percolation-harmonic-corrected.tex from the preserved arXiv v2 source
paper/percolation-harmonic.tex by surgical corrections. Each correction is an exact replacement
(asserted unique) with a `% CORRECTION [Cn]` comment line inserted above the changed line. Each
correction was tested in an independent model review; paper/CORRECTIONS.md lists them with their
reasons, and paper/open-gadget-correction.tex explains C9 and C10."""
import sys

SRC, DST = sys.argv[1], sys.argv[2]
s = open(SRC).read()

C = []  # (tag, comment, old, new)

C.append(("C1", "T_L uses x_1 <= L (|x|_inf <= L): with the l^1 norm |T_L| ~ L^2/2 and Lemma lemma:density-bound-good-event would read P[G]/2; its proof uses this triangle.",
  r"T_L := \{ x = (x_1 , x_2) \in \Z^2 \, : \, |x| \leq L, x_1 \geq |x_2|\}$",
  r"T_L := \{ x = (x_1 , x_2) \in \Z^2 \, : \, x_1 \leq L, x_1 \geq |x_2|\}$"))
C.append(("C2", "Euclidean norm in the continuum Green's function (|x| denotes the l^1 norm).",
  r"\ln |x| \quad \mbox{if~$d = 2$}",
  r"\ln |x|_2 \quad \mbox{if~$d = 2$}"))
C.append(("C2b", "Euclidean norm in the continuum Green's function.",
  r"\frac{1}{|x|^{d-2}} \quad \mbox{if~$d \geq 3$}",
  r"\frac{1}{|x|_2^{d-2}} \quad \mbox{if~$d \geq 3$}"))
C.append(("C3", "with G(y,y) = 0 the constant at infinity depends on the pole (a leaf y' attached to y gives G(x,y') = G(x,y) - 1 for x != y'); Section 5 uses the normalized Green's function H.",
  r"The first result we present is a homogenization theorem for the gradient of the Green's function.",
  r"In dimension $d = 2$, the limit $\kappa(y) := \lim_{|x| \to \infty} \left( G(x , y) - \bar G(x - y) \right)$ exists by~\cite[Theorem 2]{dario-gu-green}, and we define the \emph{normalized Green's function} $H(x , y) := G(x , y) - \kappa(y)$; it is symmetric in $x$ and $y$ (see~\cite[Section 5]{dario-gu-green}), and $\nabla_x H = \nabla_x G$. In dimension $d \geq 3$ we set $H := G$." "\n\n\t"
  r"The first result we present is a homogenization theorem for the gradient of the Green's function."))
C.append(("C4", "with the convention (id:vectorfiedledges) the printed left side is of order |grad Gbar| (e.g. at a leaf whose only neighbour is x + e_j); the orientation-consistent form uses grad of the corrected planes, which also vanishes on closed edges. In d = 2 the proof subtracts kappa(y) and the local logarithmic constant before the regularity estimates.",
  r"\left| \nabla_x G(x , y) - \nabla \bar G(x - y) - \sum_{i = 1}^d \nabla \chi_{e_i}(x) \partial_i \bar G(x - y) \right|",
  r"\left| \nabla_x G(x , y) - \sum_{i = 1}^d \nabla \ellp{e_i}(x) \partial_i \bar G(x - y) \right|"))
C.append(("C5", "sign: with the convention (id:vectorfiedledges), grad l_xi = -xi on open edges and 0 on closed edges.",
  r"and observe that $\nabla \ell_\xi = \xi + \nabla \chi_\xi = \nabla l_\xi + \nabla \chi_\xi.$",
  r"and observe that $\nabla \ell_\xi = \nabla l_\xi + \nabla \chi_\xi$, where $\nabla l_\xi(x) = -\xi$ on open edges and $\nabla l_\xi$ vanishes on closed edges."))
C.append(("C6", "the bound holds for the normalized Green's function H; in d = 2 it fails for G at a leaf. Mixed derivatives of G and H coincide.",
  r"\left| \nabla_y G(x , y) \right| \leq \frac{C \mathcal{M}_{\nabla\mathrm{-Decay}}(y)^{\frac{d}{2}}}{|x - y|^{d-1}}.",
  r"\left| \nabla_y H(x , y) \right| \leq \frac{C \mathcal{M}_{\nabla\mathrm{-Decay}}(y)^{\frac{d}{2}}}{|x - y|^{d-1}}."))
C.append(("C7", "as printed the lemma is false: two simple lattice rays from two corners of a square that merge into one ray leave a single component with N in its closure. The proof uses that the beta_i are Jordan curves.",
  r"let $\gamma_1 , \ldots, \gamma_K$ be $K$ distinct paths such that $\gamma_i(0) = x_i$ and $\gamma_i(1) = N$, and there exists a loop $\alpha$ such that, for any $i \in \{1 , \ldots, K\}$, $\alpha \cap \gamma_i = \{ x_i \}.$",
  r"let $\gamma_1 , \ldots, \gamma_K$ be simple paths such that $\gamma_i(0) = x_i$, $\gamma_i(1) = N$ and $\gamma_i \cap \gamma_j = \{ N \}$ for $i \neq j$, and let $\alpha$ be a Jordan curve with $N \notin \alpha$ such that, for any $i \in \{1 , \ldots, K\}$, $\alpha \cap \gamma_i = \{ x_i \}.$"))
C.append(("C8", "indexing: alpha_i runs from x_i to x_{i+1}; indices modulo K.",
  r"\beta_i := \gamma_{i-1} \cup \alpha_i \cup  \gamma_{i}.",
  r"\beta_i := \gamma_{i} \cup \alpha_i \cup  \gamma_{i+1} \quad \mbox{(indices modulo $K$)}."))
C.append(("C9", "paper/open-gadget-correction.tex: on the closed rectangle the claim is false (values at unused closed sites make u nonconstant without changing the terminals); it holds on the open carrier T^1_n with its induced graph.",
  r"if $u: \Tn{n} \to \Z$ is harmonic ",
  r"if $u: T^{1}_n \to \Z$ is harmonic, for the graph induced on $T^{1}_n$, at every site of $T^{1}_n \setminus \{ \sgadget , \tgadget \}$, "))
C.append(("C9b", "see C9.",
  r"in $\inte(\Tn{n})$ and non-constant, then",
  r"and non-constant, then"))
C.append(("C10", "direction of divisibility (paper/open-gadget-correction.tex): u(a) = (B_n / A_{n+1}) u(t) is an integer and gcd(A_{n+1}, B_n) = 1.",
  r"this means $u(\tgadget)$ must divide $A_{n+1}$",
  r"this means $A_{n+1}$ must divide $u(\tgadget)$ (recall $u(\sgadget) = 0$)"))
C.append(("C11", "as printed the lemma is trivial (constants, slope 0); its proof and its use (lemma:det-slope needs a nonzero slope) take a non-constant function and give |p| >= 1 after rescaling.",
  r"If the event that there exists an integer-valued harmonic function of linear growth on the cluster",
  r"If the event that there exists a non-constant integer-valued harmonic function of linear growth on the cluster"))
C.append(("C11b", "see C11.",
  r"has positive probability, then there exists a deterministic slope $\underline{p} \in \R^d$",
  r"has positive probability, then there exists a deterministic slope $\underline{p} \in \R^d$ with $|\underline{p}| \geq 1$"))
C.append(("C12", "for u -> 0 the printed limsup |u(x)|/|x| is always 0 (and the theorem false as printed: a dipole of H across an edge where l_{e_1} varies); decay at most like |x|^{-1} is limsup |x| |u(x)| > 0.",
  r"\limsup_{|x| \to \infty} \frac{|u(x)|}{|x|} > 0;",
  r"\limsup_{|x| \to \infty} |x| \, |u(x)| > 0;"))
C.append(("C13", "potential of the normalized Green's function H (see C3): with G, a leaf at a pole gives a mean-zero potential tending to a nonzero constant, and Props prop:gradient-trichotomy, prop:two-scale-expansion-mean-zero, prop:level-set-of-harmonic-function fail.",
  r"u_f(x) := \sum_{y \in \mathscr{C}_\infty} f(y) G(x , y),",
  r"u_f(x) := \sum_{y \in \mathscr{C}_\infty} f(y) H(x , y),"))
C.append(("C13b", "see C13.",
  r"where $G$ is the elliptic Green's function on $\mathscr{C}_{\infty}$. ",
  r"where $H$ is the normalized Green's function on $\mathscr{C}_{\infty}$ defined after~\eqref{eq:green-function-2D}. "))
C.append(("C14", "the representation holds for any kernel; with H (see C13).",
  r"u_f (x) = \sum_{y \in \mathscr{C}_\infty} f(y) G(x , y)  = \sum_{e \subseteq \mathscr{C}_\infty} F(e) \nabla G(x, e).",
  r"u_f (x) = \sum_{y \in \mathscr{C}_\infty} f(y) H(x , y)  = \sum_{e \subseteq \mathscr{C}_\infty} F(e) \nabla H(x, e)."))
C.append(("C15", "the proof passed from a general u to u_f without justification; the identification u = u_f is added.",
  r"As $\lim_{|x| \to \infty} u_f(x) = 0$ and $-\Delta_{\mathscr{C}_{\infty}} u_f = f \in \Z$, we must have that $f$ is compactly supported. Consequently, ",
  r"Let $u$ be as in the statement and $f := -\Delta_{\mathscr{C}_{\infty}} u$. As $\lim_{|x| \to \infty} u(x) = 0$ and $f$ is integer-valued, we must have that $f$ is compactly supported. Consequently, "))
C.append(("C15b", "see C15.",
  r"we have that $f \in \mathscr{F}$. This completes the proof by the assumption that $u_f$ decays to zero at infinity. ",
  r"we have that $f \in \mathscr{F}$. The difference $u - u_f$ is harmonic and, by Propositions~\ref{prop:not-mean-zero-log-growth} and~\ref{prop:two-scale-expansion-mean-zero}, grows sublinearly, hence it is constant by Theorem~\ref{theorem:large scale-regularity}. Since $u$ is bounded, Proposition~\ref{prop:not-mean-zero-log-growth} gives $\sum_{x \in \mathscr{C}_\infty} f(x) = 0$; then $u_f$ tends to $0$ by Proposition~\ref{prop:two-scale-expansion-mean-zero}, so $u = u_f$, and Proposition~\ref{prop:fast-decay-stronger} applies to $u$. "))
C.append(("C16", "for H (see C6); for G it fails in d = 2.",
  r"\left| \nabla_y G(x , y) \right| \leq \frac{C \mathcal{M}_{\nabla\mathrm{-Decay}}(y)^{\frac{d}{2}}}{|x - y|}.",
  r"\left| \nabla_y H(x , y) \right| \leq \frac{C \mathcal{M}_{\nabla\mathrm{-Decay}}(y)^{\frac{d}{2}}}{|x - y|}."))
C.append(("C17", "p = 0 must be excluded (l_0 is constant; noncompact mean-zero potentials exist); the proof uses the ray R p.",
  r"For any fixed slope $p \in \R^2$, almost surely on the event",
  r"For any fixed slope $p \in \R^2 \setminus \{ 0 \}$, almost surely on the event"))
C.append(("C18", "sign of the leading term: moving the pole to the source variable, grad Gbar is odd; the leading term is -sum_i M_i d_i Gbar(x).",
  r"\left| u_f (x) -  \sum_{i = 1}^d \left(\sum_{y \in \mathscr{C}_\infty} f(y) \ellp{e_i}(y) \right) \partial_i \bar G(x) \right|",
  r"\left| u_f (x) +  \sum_{i = 1}^d \left(\sum_{y \in \mathscr{C}_\infty} f(y) \ellp{e_i}(y) \right) \partial_i \bar G(x) \right|"))
C.append(("C19", "the slope p is fixed and nonzero (as in prop:gradient-trichotomy).",
  r"Almost surely, on the event that $\sum_{x \in \mathscr{C}_{\infty}} f(x) = 0$ and $|\supp u_f| = \infty$, we have that ",
  r"Fix a slope $p \in \R^2 \setminus \{ 0 \}$. Almost surely, on the event that $\sum_{x \in \mathscr{C}_{\infty}} f(x) = 0$ and $|\supp u_f| = \infty$, we have that "))
C.append(("C20", "barrier sign: G(., a) <= 0 tends to -infinity; the proof needs v >= 0 tending to +infinity.",
  r"Let $v := G(\cdot, a)$, where $G$ is the Green's function for the cluster as defined in \eqref{eq:green-function-2D}. ",
  r"Let $v := -G(\cdot, a)$, where $G$ is the Green's function for the cluster as defined in \eqref{eq:green-function-2D}; by the maximum principle $v \geq 0$, since $G(a,a) = 0$ and $G(x , a) \to -\infty$ as $|x| \to \infty$. "))
C.append(("C21", "the condition is on a component D of R^2 \\ gamma, as used in the proof (C_inf cap D subset L_0).",
  r"one of the connected components of $\mathscr{C}_{\infty} \cap (\R^2 \setminus \gamma)$ is included in $L_0$.",
  r"for one of the connected components $D$ of $\R^2 \setminus \gamma$, the set $\mathscr{C}_{\infty} \cap D$ is included in $L_0$."))
C.append(("C22", "the connectors must join all K+2 initial points.",
  r"for any $i \in \{1 , \ldots, K \}$, we may find a finite path $\tilde \gamma_i$ which connects the vertices $y_i$ and $y_{i+1}$",
  r"for any $i \in \{1 , \ldots, K+1 \}$, we may find a finite path $\tilde \gamma_i$ which connects the vertices $y_i$ and $y_{i+1}$"))
C.append(("C23", "distances from the starting point x, so that G_1(x, K) is the translate of G_1(0, K) (used in lemma:density-bound-good-event).",
  r"\left| \gamma(\mathrm{end}) \right| \geq K ~\mbox{and}~ \sum_{i = 1}^{|\gamma|} \indc_{E_R \left( \gamma(i) \right)} \geq c_1 | \gamma(\mathrm{end}) | \right\},",
  r"\left| \gamma(\mathrm{end}) - x \right| \geq K ~\mbox{and}~ \sum_{i = 1}^{|\gamma|} \indc_{E_R \left( \gamma(i) \right)} \geq c_1 | \gamma(\mathrm{end}) - x | \right\},"))
C.append(("C24", "printed '2 diam R''; read as twice the l^inf diameter 2R' of Q_{R'}(x).",
  r"\osc_{Q_{R'}(x) \cap \mathscr{C}_{\infty}} \ellp{e_1} \leq 2 \diam R' \right\}.",
  r"\osc_{Q_{R'}(x) \cap \mathscr{C}_{\infty}} \ellp{e_1} \leq 4 R' \right\}."))
C.append(("C25", "the multiplicative harmonic function equals -1 at two sites, so its eigenvalue is 1 - 4/m; the theorem is unchanged.",
  r"\frac{1}{m} \sum_{x \in \mathscr{C}_{*}(Q_n)} h(x) =  \frac{1}{m} \left( m - 2 \right) = (1 - \frac{2}{m}). ",
  r"\frac{1}{m} \sum_{x \in \mathscr{C}_{*}(Q_n)} h(x) =  \frac{1}{m} \left( m - 4 \right) = (1 - \frac{4}{m}). "))
C.append(("C25b", "see C25.",
  r"Consequently, the eigenvalue $(1 - \frac{2}{m})$ has multiplicity",
  r"Consequently, the eigenvalue $(1 - \frac{4}{m})$ has multiplicity"))
C.append(("C25c", "see C25.",
  r"\geq c m (1- \frac{2}{m})^{2 t}",
  r"\geq c m (1- \frac{4}{m})^{2 t}"))

# Gaps G1-G8 of the printed proofs (paper/CORRECTIONS.md). Applied after C1-C25, so C31 matches the
# text produced by C23.
C.append(("C26", "Lipschitz is for the chemical distance; membership in A_1 needs a chemical-distance comparison (gap G3).",
  r"Every harmonic function which is Lipschitz is contained in $\mathcal{A}_1(\mathscr{C}_{\infty})$.",
  r"Every harmonic function which is Lipschitz is contained in $\mathcal{A}_1(\mathscr{C}_{\infty})$, since, almost surely, for every $x_0 \in \mathscr{C}_\infty$ we have $\dist_{\mathscr{C}_\infty}(x_0 , x) \leq C |x - x_0|$ for all $x \in \mathscr{C}_\infty$ with $|x|$ large enough, by~\cite[Theorem 1.1]{antal-pisztora-chemical} and the Borel--Cantelli lemma."))
# There is no C27: the printed Lemma 4.8 holds (Lean: Rigidity.Assembly.Main.nonConstantOnGadget).
# C36-C36g repair its proof (gap G2) along Rigidity/Proofs/S4/OuterNonConstant; C37-C37b take from that
# proof the two facts the proof of Lemma 4.7 uses.
C.append(("C36", "gap G2: the averaging argument below resets only edges fixed by every event C_inf cap Q_R = H'; so the comparison environment keeps the edges leaving Q_R and the edges at the (d-2)-skeleton of Q_R random, and opens the faces F_R instead of closing the edges at the boundary of Q_R.",
  r"Restrict to the event that $E_R$ occurs and let $\ellp{p}$ be the corrected plane in $\mathscr{C}_{\infty}$.  Consider the infinite cluster $\mathscr{\tilde C}_{\infty}$ in the environment where every edge which contains a vertex in $\partial Q_R$ is closed",
  r"Denote by $\omega$ the environment and by $\ellp{p}$ the corrected plane in $\mathscr{C}_{\infty}$. Let $F_R$ be the set of sites of $\partial Q_R$ with exactly one coordinate in $\{-R, R\}$, and call connector edges the $4d(d-1)$ edges from a site $\pm R e_i \pm R e_j$ ($i \neq j$) to $F_R$. Let $\tilde \omega$ be obtained from $\omega$ by opening the edges between two sites of $F_R$ and the connector edges, and closing the other edges with both endpoints in $F_R \cup Q_{R-1}$. Consider the infinite cluster $\mathscr{\tilde C}_{\infty}$ of $\tilde \omega$"))
C.append(("C36b", "see C36.",
  r"As the event $E_R$ occurs, $\mathscr{\tilde C}_{\infty} \subset \mathscr{C}_{\infty}$ and each face of $Q_{R+1}$ contains a site in $\mathscr{\tilde C}_{\infty}$. Further, since $\ellp{p}$ is not constant in $Q_R$, $\tilde{\ellp{p}} $ is not constant on $Q_{R+1}$. Indeed, if this were the case, ",
  r"If $E_{R-1}$ occurs and the connector edges are open in $\omega$, then $\tilde{\ellp{p}}$ takes two values on $F_R \cap \mathscr{\tilde C}_{\infty}$. Indeed, $\omega$ and $\tilde \omega$ then differ only at edges with both endpoints in $F_R \cup Q_{R-1}$; if this were not the case, "))
C.append(("C36c", "see C36.",
  r"we could extend $\tilde{\ellp{p}}$ by a constant in $Q_{R} \cap \mathscr{C}_{\infty}$ and considering $(\ellp{p} -\tilde{\ellp{p}})$ would give rise to a non-constant, sublinear harmonic function on $\mathscr{C}_{\infty}$, contradicting ",
  r"the function $v$ equal to $\tilde{\ellp{p}}$ off $F_R \cup Q_{R-1}$ and to a constant on $(F_R \cup Q_{R-1}) \cap \mathscr{C}_{\infty}$ would be harmonic on $\mathscr{C}_{\infty}$ (at a site of $F_R$, the edges of $\tilde \omega$ to $F_R$ carry no current), and $(\ellp{p} - v)$ would be a sublinear harmonic function, non-constant as $\ellp{p}$ takes two values on $Q_{R-1} \cap \mathscr{C}_{\infty}$ (second property of $E_{R-1}$), contradicting "))
C.append(("C36d", "see C36; union bound over one face site, the other one fixed.",
  r"Let $\tilde x$ and $\tilde y$ be sites on opposite faces of $Q_{R+1} \cap \mathscr{\tilde C}_{\infty}$ for which $\tilde{\ellp{p}} (\tilde x) \neq \tilde{\ellp{p}}(\tilde y)$ and let $x$ and $y$ be sites  in $Q_R \cap \mathscr{C}_{\infty}$ which, respectively, share an edge with $\tilde x$ and $\tilde y$.",
  r"Let $\tilde y := (1, -R, 0, \ldots, 0)$. As $F_R$ is connected in $\tilde \omega$ and $\P[E_{R-1}] \to 1$, for $R$ large, with probability at least $\frac12 \mathfrak{p}^{4d(d-1)}$ there is $\tilde x \in F_R$ with $\tilde x, \tilde y \in \mathscr{\tilde C}_{\infty}$ and $\tilde{\ellp{p}}(\tilde x) \neq \tilde{\ellp{p}}(\tilde y)$. By a union bound over $\tilde x \in F_R$, we fix $\tilde x$ so that this event $W$ has $\P[W] \geq \frac12 \mathfrak{p}^{4d(d-1)} |Q_R|^{-1} \geq c R^{-d}$, and we let $x$ and $y$ be the sites of $Q_{R-1}$ which, respectively, share an edge with $\tilde x$ and $\tilde y$."))
C.append(("C36e", "see C36.",
  r"Let $P_1$ and $P_2$ be paths in $\Z^d$ from",
  r"Let $P_1$ and $P_2$ be disjoint paths in $Q_{R-1}$ from"))
C.append(("C36f", "see C36.",
  r"Let $H = P_1 \cup P_2$ together with a subgraph of $Q_{R/2} \cup \{s, a, b, t\}$ which is isometric to $\Tn{R}$.",
  r"Let $H = P_1 \cup P_2$ together with a subgraph of $Q_{R/2} \cup \{s, a, b, t\}$ which is isometric to $\Tn{R}$. Let $\omega'$ be obtained from $\tilde \omega$ by opening the edges of $H$, $\{x, \tilde x\}$ and $\{y, \tilde y\}$, and closing the other edges at the sites of $H$; on $W$ its infinite cluster is $\mathscr{\tilde C}_{\infty} \cup H$."))
C.append(("C36g", "gap G2: conditioning on C_inf cap Q_R = H' reweights the edges the proof leaves free; averaging over H' after resetting a finite set D of edges fixed by every such event gives the conditional bound (Lean: Rigidity/Proofs/S4/OuterNonConstant/Reset.lean, exists_conditional_ge).",
  r"By taking a union bound over all possible choices of boundary placements $x$ and $y$, we have the desired claim.",
  r"Hence, on $W$, ${\ellp{p}}'$ is not constant on $\Tn{R}$, through which the current between $x$ and $y$ flows. Let $D$ be the set of the connector edges and of the edges with both endpoints in $F_R \cup Q_{R-1}$ and one endpoint in $F_R$ or at a site of $H$; let $\omega^D$ be equal to $\omega'$ (deterministic on $D$) on $D$ and to $\omega$ elsewhere, and $B := \{ \omega = \omega^D \}$. The other edges of $Q_{R-1}$ do not meet the infinite cluster, so $G := \{ \ellp{p} ~\mbox{is not constant on}~ \Tn{R} \}$ satisfies $\P[\omega^D \in G] \geq \P[W] \geq c R^{-d}$; $B$ is independent of $\omega^D$ and $B \cap G = B \cap \{ \omega^D \in G \}$. Let $\mathcal{H}$ be the set of the $H' := \mathscr{C}_{\infty}(\omega^D) \cap Q_R$ with $\omega^D \in G$, and $A_{H'} := \{ \mathscr{C}_{\infty} \cap Q_R = H' \}$. Then $\Tn{R}$, hence $H$ and $F_R$, lie in $\mathscr{C}_{\infty}(\omega^D)$, so each edge of $D$ has an endpoint at a site of $H'$ and, on $A_{H'}$, is open if and only if it lies in $H'$: $A_{H'} \subset B$. As the events $A_{H'}$ are disjoint, $\sum_{H' \in \mathcal{H}} \P[A_{H'} \cap G] \geq \P[B \cap G] = \P[B] \, \P[\omega^D \in G] \geq \P[\omega^D \in G] \sum_{H' \in \mathcal{H}} \P[A_{H'}]$. Since $|\mathcal{H}| \leq 2^{(d+1) |Q_R|}$, the $H'$ with $\P[A_{H'}] < \delta := 2^{-(d+1)|Q_R| - 1} \P[B] \, \P[\omega^D \in G]$ contribute at most half of the left side; hence some $H' \in \mathcal{H}$ has $\P[A_{H'}] \geq \delta \geq \exp(-C R^d)$ and $\P[ G \, | \, A_{H'} ] \geq \frac12 \P[\omega^D \in G] \geq c R^{-2d+2}$. As every edge at a site of $\Tn{R}$ lies in $D$, $\Tn{R}$ is an induced subgraph of $H'$, attached to the rest of $H'$ at its two terminals only: the claim holds with $H'$ in place of $H$."))
C.append(("C37", "the event C_inf cap Q_R = H depends on the edges outside Q_R, so its probability is not a product over the sites of Q_R; the proof of lemma:non-constant-on-gadget gives the lower bound, and the isolation of the gadget needed by prop:exponential-growth-gadget.",
  r"Using that the probability of the event $\mathscr{C}_\infty \cap Q_R = H$ is lower bounded by $\min( \mathfrak{p}, 1 - \mathfrak{p})^{\left| Q_R \right|}$, we deduce that",
  r"Here, by the proof of Lemma \ref{lemma:non-constant-on-gadget}, $H$ can be chosen with $\Tn{R}$ attached to the rest of $H$ at its two terminals only, as Proposition \ref{prop:exponential-growth-gadget} requires, and with $\P[\mathscr{C}_\infty \cap Q_R = H] \geq \exp(-C R^d)$; we deduce that"))
C.append(("C37b", "see C37.",
  r"\min( \mathfrak{p}, 1 - \mathfrak{p})^{\left|Q_R\right|}  \geq c \exp \left( - C R^d \right).",
  r"\exp \left( - C R^d \right)  \geq c \exp \left( - 2 C R^d \right)."))
C.append(("C28", "measurability of E, needed for the ergodic theorem (gap G4).",
  r"By the ergodic theorem, we have that almost surely, ",
  r"The event $E$ is the projection to $\Omega$ of a Borel subset of $\Omega \times \Z^{\Z^d}$; it is therefore analytic, hence measurable for the completion of $\P$, to which the ergodic theorem applies. By the ergodic theorem, we have that almost surely, "))
C.append(("C28b", "nonconstancy of v (gap G4).",
  r"constructed a non-trivial integer-valued harmonic function of linear growth, ",
  r"constructed an integer-valued harmonic function of linear growth, which is non-constant since $2 M (y^+ - y^-) \neq 0$ and, almost surely, $\mathscr{C}_\infty$ is not contained in an $o(|x|)$-neighbourhood of a hyperplane, "))
C.append(("C29", "Step 3 of the proof of prop:gradient-trichotomy gives E[1_E N_k]/|B_{2^k}| -> 0, which by Fatou contradicts a positive lower limit but not a positive upper limit (typewriter sequence); the proof of this proposition (lemma:density-bound-good-event) gives the lower limit (gap G8).",
  r"\limsup_{k \to \infty}  \frac{1}{|B_{2^k}|} \left| \left\{ e \in E(B_{2^k}) : \nabla u_f(e) \neq 0 \mbox{ and }",
  r"\liminf_{k \to \infty}  \frac{1}{|B_{2^k}|} \left| \left\{ e \in E(B_{2^k}) : \nabla u_f(e) \neq 0 \mbox{ and }"))
C.append(("C29b", "see C29.",
  r"which contradicts \eqref{eq:level-set-of-harmonic-function} except if $\P(E) = 0$.",
  r"which, by Fatou's lemma, contradicts \eqref{eq:level-set-of-harmonic-function} except if $\P(E) = 0$."))
C.append(("C30", "the printed proof of prop:level-set-of-harmonic-function treats p = e_1 only (the counting uses grad l_{e_1}); the statement holds for every fixed p != 0 with these changes (gap G7).",
  r"We introduce the good event which we will use in the next subsection, together with the ",
  r"We write the proof of Proposition~\ref{prop:level-set-of-harmonic-function} for $p = e_1$. For a fixed $p \neq 0$, replace $\ellp{e_1}$ by $\ellp{p}$ throughout, the bound $4 R'$ in the event $G_2$ below by $\Lambda_p R'$ for a constant $\Lambda_p$ depending on $p$, the cone $\{ x_1 \geq |x_2| \}$ by $\{ p \cdot x \geq \kappa |x| \}$ for a small $\kappa > 0$, and the half-line $L_-$ by a lattice half-line $\{ - n v \, : \, n \in \N \}$ with $v \in \{ \pm e_1 , \pm e_2 \}$ and $p \cdot v > 0$; the lower bound on $\P[G_3]$ uses that $\P[ |\nabla \ellp{p}(0)| > L ] > 0$ for every $L$, which follows from Theorem~\ref{theorem:lipschitz} and stationarity. We introduce the good event which we will use in the next subsection, together with the "))
C.append(("C31", "printed with an existential over gamma: then G_1(x, K) lies in {x in C_inf} and eq:PG1goesto1 fails (P <= theta(p) < 1), and Step 6 of lemma:large-gradient-implies-not-in-level-set applies G_1 to a given path; the complement of the universal event is the event of prop:longpathsupercritrenormlatt (gap G6).",
  r"\left\{ \exists \gamma \subseteq \mathscr{C}_\infty \, \mbox{ with } \gamma(0) = x ,~  \left| \gamma(\mathrm{end}) - x \right| \geq K ~\mbox{and}~ \sum",
  r"\left\{ \forall \gamma \subseteq \mathscr{C}_\infty \, \mbox{ with } \gamma(0) = x ~\mbox{and}~  \left| \gamma(\mathrm{end}) - x \right| \geq K , ~ \sum"))
C.append(("C32", "Prop prop:not-lipschitz bounds |grad l_{e_1}(0)| without sign or direction, and the symmetries fixing the slope e_1 preserve the sign of l(x+e_1) - l(x), so the printed event (the edge (x, x+e_1)) is not shown to have positive probability; the proof of lemma:large-gradient-implies-not-in-level-set uses x + e_1 only as a neighbour of x (gap G5).",
  r"which is satisfied if the edge $(x, x+e_1)$ is open in the infinite cluster and if the corrector has",
  r"which is satisfied if, for some neighbour $x'$ of $x$, the edge $(x, x')$ is open in the infinite cluster and the corrected plane has"))
C.append(("C32b", "see C32.",
  r"gradient larger than $C_\chi$ across the edge $(x, x+e_1)$. It is formally defined as",
  r"an increment larger than $C_\chi$ across the edge $(x, x')$. It is formally defined as"))
C.append(("C32c", "see C32.",
  r"G_3(x,  C_{\chi}) := \left\{  (\ellp{e_1}(x + e_1) - \ellp{e_1}(x) )\indc_{(x, x+e_1) \in E(\mathscr{C}_\infty)} \geq C_\chi  \right\}.",
  r"G_3(x,  C_{\chi}) := \left\{ \exists x' \sim x \, : \, (x , x') \in E(\mathscr{C}_\infty) ~\mbox{and}~ \ellp{e_1}(x') - \ellp{e_1}(x) \geq C_\chi  \right\}."))
C.append(("C32d", "see C32.",
  r"Theorem~\ref{theorem:lipschitz} and symmetry arguments ensure that this assumption can be made without loss of generality.",
  r"By Proposition~\ref{prop:not-lipschitz}, $\P[ |\nabla \ellp{e_1}(0)| > 2 C_\chi ] > 0$; on this event some edge $(0 , e_i) \in E(\mathscr{C}_\infty)$, $i \in \{1 , 2\}$, satisfies $|\ellp{e_1}(e_i) - \ellp{e_1}(0)| > C_\chi$, so that $G_3(0 , C_\chi)$ or $G_3(e_i , C_\chi)$ holds, and by stationarity $\P[G_3(0 , C_\chi)] > 0$."))
C.append(("C32e", "see C32.",
  r"and by Proposition \ref{prop:not-lipschitz}, $\P[G_3(0 , C_\chi)] \geq c(\mathfrak{p}, C_{\chi}) > 0$.",
  r"and by the discussion following~\eqref{eq:not-lipschitz}, $\P[G_3(0 , C_\chi)] \geq c(\mathfrak{p}, C_{\chi}) > 0$."))
C.append(("C32f", "see C32.",
  r"and define $e = (x_0 , x_0 + e_1) \in E\left( \mathscr{C}_\infty \right).$",
  r"and let $x_1$ be a neighbour of $x_0$ given by the event $G_3(x_0 , C_\chi)$. To keep the notation of the printed proof, we write $x_0 + e_1$ for $x_1$ in the rest of this proof; the argument uses only that $(x_0 , x_1) \in E(\mathscr{C}_\infty)$ and $\ellp{e_1}(x_1) - \ellp{e_1}(x_0) \geq C_\chi$. Define $e = (x_0 , x_0 + e_1) \in E\left( \mathscr{C}_\infty \right).$"))
C.append(("C33", "Jerison-Levine-Pike, Theorem 4.3, concerns the chain with holding probability 1/(m+1) on a simple graph; for the chain defined above the cited bound fails when every site has an even number of exits (eigenvalue -1). The theorem holds with the single-exit argument (gap G1).",
  r"By \cite[Theorem 4.3]{jerison-levine-pike-2019}, writing $m := |\mathscr{C}_{*}(Q_n)|$ we have",
  r"Almost surely, for $n$ large enough, some site $x_0 \in \mathscr{C}_{*}(Q_n)$ has exactly one neighbour in $\mathscr{C}_\infty \setminus Q_n$ (a face site of $\mathscr{C}_{*}(Q_n)$ whose outward edge is open). By \cite[Theorems 3.8 and 4.1]{jerison-levine-pike-2019} and Micciancio--Regev [SIAM J. Comput. 37 (2007), Lemma 3.3], adapted to the chain defined above, which adds the chip at a uniform site of $\mathscr{C}_{*}(Q_n)$ (in \cite{jerison-levine-pike-2019} it is added at a uniform vertex including the sink, on a simple graph): harmonicity at $x_0$ of the multiplicative harmonic function $h = e^{2 \pi i (\theta + \delta)}$ gives $\dist(\theta , \Z) \leq C_d \| \delta \|_2$, which bounds the sink coordinate in the proof of \cite[Theorem 3.8]{jerison-levine-pike-2019}. Writing $m := |\mathscr{C}_{*}(Q_n)|$ we obtain"))
C.append(("C33b", "see C33.",
  r"\mbox{for all $t \geq  (5/4) m \log \left( 2 (m-1)(1 + 1/\varepsilon) \right)$}",
  r"\mbox{for all $t \geq  C_d \, m \log \left( 2 m (1 + 1/\varepsilon) \right)$}"))

# Literature inputs: the citations checked against their sources.
C.append(("C34", "the proof of prop:homogenizationellipticgreen (eq. large scale-regularity) uses the local estimate of the cited theorem, part (iii) of Theorem 2 in arXiv:1609.09431v2, which the quotation omitted.",
  r"the inequality \eqref{eq:harmonic-approximation} holds.",
  r"the inequality \eqref{eq:harmonic-approximation} holds." "\n\t\t\t"
  r"\item For each $k \in \N$, there exists a constant $C_k(k, d, \mathfrak{p}) < \infty$ such that, for every $R \geq 2 \mathcal{M}_{\mathrm{reg}}(x)$ and every $u \in \mathcal{A}(\mathscr{C}_{\infty} \cap B_R(x))$, there exists $\phi \in \mathcal{A}_k(\mathscr{C}_{\infty})$ such that, for every $r \in [\mathcal{M}_{\mathrm{reg}}(x) , \frac12 R]$, $\| u - \phi \|_{\underline{L}^2(\mathscr{C}_{\infty} \cap B_r(x))} \leq C_k \left( \frac{r}{R} \right)^{k+1} \| u \|_{\underline{L}^2(\mathscr{C}_{\infty} \cap B_R(x))}$."))
C.append(("C35", "Penrose-Pisztora 1996, Theorem 1, concerns continuum percolation, and their lattice results are for site percolation; the density estimate for bond percolation in every d >= 2 is Dario-Gu, Proposition A.1, with a union bound over the triadic cubes inside the balls.",
  r"The second one is a density estimate for the infinite cluster due to~\cite[Theorem 1]{penrose-pisztora-1996}: ",
  r"The second one is a density estimate for the infinite cluster, which follows from~\cite[Proposition A.1]{dario-gu-green} by a union bound over triadic cubes: "))

# Lemmas 2.13 and 2.14 (quoted from the literature).
C.append(("C38", "as printed the lemma is false for a constant loop (one component) or a figure-eight (three components); the Jordan curve theorem is for simple loops, and the two components are disjoint.",
  r"Let $\gamma$ be a continuous loop on $\S^2$, then the set $\S^2 \setminus \gamma$ is the union of two finite open simply connected components",
  r"Let $\gamma$ be a Jordan curve (a simple loop) on $\S^2$, then the set $\S^2 \setminus \gamma$ is the union of two disjoint open simply connected components"))
C.append(("C39", "the domain lies in the plane R^2, as in the cited remark of Rudin; a subset of Z^2 is not a domain.",
  r"Let $\Omega \subseteq \Z^2$ be a simply connected bounded domain",
  r"Let $\Omega \subseteq \R^2$ be a simply connected bounded domain"))

EXPECT = {"C1": 2}
for tag, comment, old, new in C:
    n = s.count(old)
    if n != EXPECT.get(tag, 1):
        sys.exit(f"{tag}: expected {EXPECT.get(tag, 1)} occurrence(s), found {n}")
    for _ in range(n):
        i = s.index(old)
        ls = s.rfind("\n", 0, i) + 1
        line = s[ls:]
        indent = line[:len(line) - len(line.lstrip("\t "))]
        s = s[:ls] + f"{indent}% CORRECTION [{tag}]: {comment}\n" + s[ls:]
        s = s.replace(old, new, 1)

# Five header lines, as before, so that line numbers in the body are unchanged.
header = ("% Corrected draft of arXiv:2303.04736v2. The preserved source is paper/percolation-harmonic.tex;\n"
          "% every change here is a surgical correction, marked by a comment `% CORRECTION [Cn]` above the\n"
          "% changed line. Each correction was tested in an independent model review; paper/CORRECTIONS.md\n"
          "% lists the corrections with their reasons, and paper/open-gadget-correction.tex explains C9\n"
          "% and C10. This file is generated by paper/make_corrected.py.\n")
open(DST, "w").write(header + s)
print(f"applied {len(C)} corrections")
