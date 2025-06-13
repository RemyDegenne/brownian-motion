# Lean formalization of a Brownian motion

Our goal is to formalize Brownian motions in Lean using Mathlib.
There are two main parts to this formalization:

* develop the theory of Gaussian distributions, build a projective family of Gaussian distributions and define its projective limit by the Kolmogorov extension theorem,

* prove the Kolmogorov-Chentsov continuity theorem.

Putting the two sides together, we can then build a stochastic process that fits the definition of a Brownian motion on the real line.

For more information, see [the project home page](https://remydegenne.github.io/brownian-motion/), in particular the [blueprint](https://remydegenne.github.io/brownian-motion/blueprint/).

Zulip channel for discussion: [zulip link](https://leanprover.zulipchat.com/#narrow/channel/509433-Brownian-motion)

The project is ongoing and contributions are welcome.

Our github project uses the [Leanblueprint](https://github.com/PatrickMassot/leanblueprint) tool by Patrick Massot and a lot of code from the [LeanProject](https://github.com/pitmonticone/LeanProject) template by Pietro Monticone.
