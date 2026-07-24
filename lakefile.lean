import Lake
open Lake DSL

package mgql where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib MGQL where
  roots := #[`MGQL]

lean_exe ldbcBench where
  root := `MGQL.LDBCBench
