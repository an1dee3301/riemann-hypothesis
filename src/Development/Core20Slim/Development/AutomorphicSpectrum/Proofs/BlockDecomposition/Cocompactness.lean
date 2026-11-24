module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCuspidalNeZero
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelWeilUnitaryConvergentOfSiegelWeilConvergen
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU PositivityTheory.Rg.Mass

namespace GlobalTheory.CompanionTheory.MassCocompact

theorem coCpt : CoCpt := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hCM hJ hA _ _ hμ h𝓕 _ _
  have hW : GlobalTheory.SiegelSet.IsWittFrame σ J (0 : Matrix (Fin 2) (Fin 0) E) 0 :=
    ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, fun z _ _ hz => hA z hz⟩
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.SiegelSet.Model.compact_quotient GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary hCM hJ hW
  refine ⟨⟨C, hC, fun h => ?_⟩, ?_, ?_⟩
  · obtain ⟨γ, hγ, c, hc, e⟩ := hcov h
    exact ⟨⟨γ, hγ⟩, c, hc, e⟩
  · exact (GlobalTheory.SiegelWeilConvCompare.measure_fundamentalDomain_pos F E σ 2 J μ hμ 𝓕 h𝓕).ne'
  · exact (((GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hCM 2 J hJ).2 μ hμ).2 𝓕 h𝓕).ne

end GlobalTheory.CompanionTheory.MassCocompact

end
