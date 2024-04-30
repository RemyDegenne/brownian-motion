import Lake
open Lake DSL

package «brownian_motion» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
  -- add any additional package configuration options here

require kolmogorov_extension4 from git
  "https://github.com/RemyDegenne/kolmogorov_extension4"

@[default_target]
lean_lib «BrownianMotion» where
  -- add any library configuration options here
