module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjArchOfInfEmbArchPi
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactIwasawa
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingleMulSingle
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryAdelicIwasawaCompactStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitarySiegelDomainExistsStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormSiegelBoundStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormRapidDecayStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.SiegelRed

theorem siegelCore : SiegelCore := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  obtain ⟨K₁, h₁, c₁, i₁, g₁⟩ := GlobalTheory.CompanionTheory.SiegelArch.exists_kInf F E σ h n J hJ r X Y hW
  obtain ⟨K₂, h₂, c₂, i₂, g₂⟩ := GlobalTheory.T.unitary_adelic_iwasawa_compact F E σ h n J hJ r X Y hW
  obtain ⟨K, hK, hI, hG⟩ := GlobalTheory.CompanionTheory.SiegelAssemble.exists_compact_iwasawa F E σ h n J hJ r X Y hW K₁ K₂ h₁ h₂ c₁ c₂
    i₁ i₂ g₁ g₂
  obtain ⟨Ω, c, hΩ, hΩP, hc, hcov⟩ := GlobalTheory.T.unitary_siegel_domain_exists F E σ h n J hJ r X Y hW K hK hI hG
  exact ⟨K, Ω, c, hK, hΩ, hΩP, hc, hI, hG, hcov,
    GlobalTheory.CompanionTheory.SiegelConj.conj_compact F E σ h n J hJ r X Y hW Ω c hΩ hΩP hc,
    GlobalTheory.T.cusp_form_siegel_bound F E σ h n J hJ r X Y hW K Ω c hK hΩ hΩP hc,
    GlobalTheory.T.cusp_form_rapid_decay F E σ h n J hJ r X Y hW K Ω c hK hΩ hΩP hc⟩

theorem siegelSetUnitary : GlobalTheory.Published.SiegelSetUnitary :=
  siegel_of_core siegelCore

end GlobalTheory.CompanionTheory.SiegelRed
