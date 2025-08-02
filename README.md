# Lean formalization of a Brownian motion

This project contains the formalization of a standard Brownian motion in Lean using Mathlib.
There are two main parts to this formalization:

* a development of the theory of Gaussian distributions, the construction of a projective family of Gaussian distributions and its projective limit by the Kolmogorov extension theorem,

* a proof of a Kolmogorov-Chentsov continuity theorem.

Putting the two sides together, we then build a stochastic process that fits the definition of a Brownian motion on the real line.

For more information, see [the project home page](https://remydegenne.github.io/brownian-motion/), in particular the [blueprint](https://remydegenne.github.io/brownian-motion/blueprint/).

The construction of the Brownian motion has been completed, and we are currently exploring further directions.
See this Zulip channel for discussion: [zulip link](https://leanprover.zulipchat.com/#narrow/channel/509433-Brownian-motion)

Our github project uses the [Leanblueprint](https://github.com/PatrickMassot/leanblueprint) tool by Patrick Massot and a lot of code from the [LeanProject](https://github.com/pitmonticone/LeanProject) template by Pietro Monticone.

If you use this work, please cite it using the data provided in the CITATION.cff file.
