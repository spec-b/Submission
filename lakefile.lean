import Lake
open Lake DSL

package «lean-cond» {
  -- add package configuration options here
}

lean_lib «LeanCond» {
  -- add library configuration options here
}

@[default_target]
lean_lib «lean-cond» {

}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"
