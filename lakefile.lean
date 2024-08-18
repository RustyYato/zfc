import Lake
open Lake DSL

package "zfc" where
  -- add package configuration options here

lean_lib «Zfc» where
  -- add library configuration options here

@[default_target]
lean_exe "zfc" where
  root := `Main
