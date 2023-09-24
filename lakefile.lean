import Lake
open Lake DSL

package «brownian_motion» {
  -- add package configuration options here
}

require kolmogorov_extension4 from git
  "https://github.com/RemyDegenne/kolmogorov_extension4"

@[default_target]
lean_exe «brownian_motion» {
  root := `Main
}
