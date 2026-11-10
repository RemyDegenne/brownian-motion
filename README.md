# Lean formalization of Brownian motion and stochastic integrals

This is an open, collaborative project with the goal of formalizing stochastic processes and stochastic integration in Lean.
There are currently two main parts:

* A formalization of Brownian motion, which is now complete. That task needed a development of the theory of Gaussian distributions, the construction of a projective family of Gaussian distributions and its projective limit by the Kolmogorov extension theorem, and a proof of a Kolmogorov-Chentsov continuity theorem.

* A definition of stochastic integrals and proof of Ito's lemma. This is in progress.

For more information, see [the project home page](https://remydegenne.github.io/brownian-motion/), in particular the [blueprint](https://remydegenne.github.io/brownian-motion/blueprint/).


### Brownian motion

We now have a full implementation of a Brownian motion on the positive real half line, and are in the process of migrating our results to Mathlib.
See [that page](https://remydegenne.github.io/brownian-motion/verso/) for a brief overview of the results.

We also have a preprint, available at [https://arxiv.org/pdf/2511.20118](https://arxiv.org/pdf/2511.20118). To cite our work on Brownian motion, please use the following BibTex entry:
```
@article{degenne2025formalization,
  title={Formalization of Brownian motion in Lean},
  author={Degenne, R{\'e}my and Ledvinka, David and Marion, Etienne and Pfaffelhuber, Peter},
  journal={arXiv preprint arXiv:2511.20118},
  year={2025}
}
```


### Stochastic integrals

We are now building the necessary theory to define the integral against a semi-martingale, with the goal to then prove Ito's lemma.
See this Zulip channel for discussion: [zulip link](https://leanprover.zulipchat.com/#narrow/channel/509433-Brownian-motion)

If you want to get involved, you can look at [the open issues](https://github.com/RemyDegenne/brownian-motion/issues). Please read the CONTRIBUTING file to learn how to claim an issue.
To see what we will need and where we are going, you can refer to the [blueprint](https://remydegenne.github.io/brownian-motion/blueprint/index.html), which we gradually refine alongside the Lean code.


### Acknowledgements

Our github project uses the [Leanblueprint](https://github.com/PatrickMassot/leanblueprint) tool by Patrick Massot and a lot of code from the [LeanProject](https://github.com/pitmonticone/LeanProject) template by Pietro Monticone.
