import Lake
open Lake DSL

def moreServerArgs := #[
  "-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
  "-DautoImplicit=false",
  "-DrelaxedAutoImplicit=false"
]

-- These settings only apply during `lake build`, but not in VSCode editor.
def moreLeanArgs := moreServerArgs

package mil where
  moreServerArgs := moreServerArgs
  moreLinkArgs := #["-L./lake-packages/LeanInfer/build/lib", "-lonnxruntime", "-lstdc++"]

@[default_target]
lean_lib MIL where
  moreLeanArgs := moreLeanArgs

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"
require llmaesop from git "https://github.com/Peiyang-Song/aesop"@"peiyang-LeanInfer-dev"
