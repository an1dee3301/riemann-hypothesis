module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TotallyRealIntegralBasisExists
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totally_real_integral_basis_exists : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → Nonempty (Module.Basis (InfinitePlace F) ℤ (𝓞 F)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.exists_integralBasis_infinitePlace | exact GlobalTheory.CompanionTheory.SW.ThW.exists_integralBasis_infinitePlace | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.exists_integralBasis_infinitePlace <;> assumption)
