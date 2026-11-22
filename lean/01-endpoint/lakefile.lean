import Lake
open Lake DSL

package fixedEvenEndpoints

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d7317655e2826dc1f1de9a0c138db2775c4bb841"

@[default_target]
lean_lib EndpointErrors where
  roots := #[`PaperFourier, `FourierWindow, `Orthogonality, `PrimeEndpoint,
    `PrincipalMass, `CubicEndpoint, `CubicRate, `PrimePowerError,
    `StepIntegral, `SieveWeight, `NonprincipalEndpoint, `CubicMangoldt,
    `ExactCutoff, `MangoldtRate, `ZeroTriple, `SingleEndpoint,
    `ExactPollution, `SignedContrast, `SquareCutoff]
