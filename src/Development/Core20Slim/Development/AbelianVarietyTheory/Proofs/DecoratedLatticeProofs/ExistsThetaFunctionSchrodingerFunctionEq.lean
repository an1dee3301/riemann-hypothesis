module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffOfHeisenbergDerivativeClosedClassStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaSeriesLawAndLevelStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSeriesSchwartzBruhatContinuousSchrodingerStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtHeisenbergThetaSeriesStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

namespace GlobalTheory.SchwOnto

noncomputable def ser (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (φ : Mx D B.rank A.rank → ℂ) :
    WO (dblSp A) B → ℂ := fun w =>
  ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ (HMul.hMul w (dblDec A).jX + rat ξ)

theorem schw_onto : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ φ : Mx D B.rank A.rank → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → ∃ f, IsThetaFunO ψ (dblSp A) B f ∧ sch ψ A B ν 𝓨 f = φ := by
  intro D ψ hψ A B ν 𝓨 hν φ hφ
  have hlaw := GlobalTheory.T.doubled_theta_series_law_and_level D ψ hψ A B φ hφ (ser D ψ A B φ) (fun _ => rfl)
  have hcs := GlobalTheory.T.thetaSeries_schwartzBruhat_continuous_schrodinger D ψ hψ A B ν 𝓨 hν φ hφ (ser D ψ A B φ) (fun _ => rfl)
  let V : Set (WO (dblSp A) B → ℂ) := {g | ∃ φ', GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' ∧ g = ser D ψ A B φ'}
  have hVc : ∀ g ∈ V, Continuous g := by
    rintro g ⟨φ', hφ', rfl⟩
    exact (GlobalTheory.T.thetaSeries_schwartzBruhat_continuous_schrodinger D ψ hψ A B ν 𝓨 hν φ' hφ' (ser D ψ A B φ') (fun _ => rfl)).1
  have hVd : ∀ g ∈ V, ∀ M : ℝ →+ WO (dblSp A) B, Continuous M → (∀ t, (M t).map (finPart D) = 0) →
      ∃ g' ∈ V, ∀ w, HasDerivAt (fun t : ℝ => heisO ψ (dblSp A) B (M t) g w) (g' w) 0 := by
    rintro g ⟨φ', hφ', rfl⟩ M hM hMf
    obtain ⟨φ'', hφ'', hd⟩ := GlobalTheory.T.hasDerivAt_heisenberg_thetaSeries D ψ hψ A B φ' hφ' (ser D ψ A B φ') (fun _ => rfl) M hM hMf
    exact ⟨ser D ψ A B φ'', ⟨φ'', hφ'', rfl⟩, hd (ser D ψ A B φ'') (fun _ => rfl)⟩
  have hsm := GlobalTheory.T.contDiff_of_heisenbergDerivativeClosedClass D ψ hψ (dblSp A) B V hVc hVd (ser D ψ A B φ) ⟨φ, hφ, rfl⟩
  exact ⟨ser D ψ A B φ, { quasi := hlaw.1, level := hlaw.2, cont := hcs.1, smooth := hsm }, hcs.2⟩

end GlobalTheory.SchwOnto
