import Lake

open Lake DSL

package PrimeWorldsFormal

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @
  "ba9c63d0fefca8bc3961f7f6e7a30ec6988a4338"

@[default_target]
lean_lib PrimeWorldsFormal
