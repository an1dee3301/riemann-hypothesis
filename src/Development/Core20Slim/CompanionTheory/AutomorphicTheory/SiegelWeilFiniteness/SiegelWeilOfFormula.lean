module

public import Development.Core20Slim.CompanionTheory.AutomorphicTheory.SiegelWeilFiniteness.AdelicCovolumeFinite
public import Development.Core20Slim.CompanionTheory.AutomorphicTheory.SiegelWeilFiniteness.Bridge
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace CompanionTheory.SWFin

open HeckeCharacterZeroLocus.SiegelWeilU

theorem finVol (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) : FinVol F E σ M J :=
  finVol_of (fun _ _ _ _ _ _ _ _ _ _ _ h => adelicCovolumeFinite h _) F E σ hσ M J hJ

end CompanionTheory.SWFin
