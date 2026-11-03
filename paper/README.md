# The paper

This directory holds the paper that the Lean development formalizes:

> Ahmed Bou-Rabee, William Cooperman and Paul Dario,
> *Rigidity of harmonic functions on the supercritical percolation cluster*,
> Transactions of the American Mathematical Society 378(6) (2025), 3823–3896,
> [doi:10.1090/tran/9264](https://doi.org/10.1090/tran/9264);
> [arXiv:2303.04736](https://arxiv.org/abs/2303.04736).

It is included with the permission of its authors and is not covered by the Apache license of the
Lean code.

| File | Content |
| --- | --- |
| [`percolation-harmonic.tex`](percolation-harmonic.tex) | The LaTeX source of arXiv:2303.04736v2, unmodified. |
| [`percolation-harmonic.pdf`](percolation-harmonic.pdf) | That source, compiled. |
| [`percolation-harmonic-corrected.tex`](percolation-harmonic-corrected.tex) | The corrected draft that the Lean statements follow: the arXiv v2 source with local corrections, each marked by a comment `% CORRECTION [Cn]` above the changed line. |
| [`percolation-harmonic-corrected.pdf`](percolation-harmonic-corrected.pdf) | The corrected draft, compiled. |
| [`CORRECTIONS.md`](CORRECTIONS.md) | The list of corrections, with the reason for each and the gaps of the printed proofs that they repair, and the three places where the Lean proofs depart from the printed argument. Each correction was tested in an independent model review. The [README](../README.md#corrections-to-the-published-version) of the repository summarizes them. |
| [`make_corrected.py`](make_corrected.py) | Produces the corrected draft from the arXiv v2 source by applying the corrections; each is an exact replacement that must occur exactly once. |
| [`open-gadget-correction.tex`](open-gadget-correction.tex) | A self-contained note on Proposition 4.1: the printed claim on the closed rectangle is false, and the note states and proves it on the open gadget with its induced graph, with the direction of divisibility used in the proof (corrections C9 and C10). |
| [`defs.tex`](defs.tex) | The macros of the arXiv source, read by both versions of the paper. |
| [`Figures/`](Figures/) | The 36 figures of the arXiv source that the paper uses. |
| [`percolation-harmonic.bbl`](percolation-harmonic.bbl), [`percolation-harmonic-corrected.bbl`](percolation-harmonic-corrected.bbl) | The bibliography of the arXiv source, one identical copy for each version of the paper. |

To regenerate the corrected draft, run from the repository root

```bash
python3 paper/make_corrected.py paper/percolation-harmonic.tex paper/percolation-harmonic-corrected.tex
```

To rebuild either PDF, run `pdflatex` three times on its `.tex` file in this directory; BibTeX is not
needed. Both versions compile without errors and without LaTeX warnings.
