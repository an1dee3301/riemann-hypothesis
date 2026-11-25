module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.AutomorphicTheory.SiegelWeilFiniteness.SiegelWeilOfFormula
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem finVol_unitaryGroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVol F E σ M J :=
  fun F E _ _ _ _ _ σ hσ M J hJ => CompanionTheory.SWFin.finVol F E σ hσ M J hJ

end GlobalTheory.CompanionTheory.SW
