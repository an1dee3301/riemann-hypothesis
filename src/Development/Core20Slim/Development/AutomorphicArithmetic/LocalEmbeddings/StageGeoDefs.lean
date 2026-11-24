module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
public import Development.Core20Slim.Development.AutomorphicArithmetic.LocalEmbeddings.ComplEquivEvW
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.StageGeo

variable {D : D7}

def AUnit {v : HeightOneSpectrum (𝓞 D.host.F)} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v) : Prop :=
  (∃ a ∈ D.host.AA, Valued.v (t a) = 1) ∧ ∃ z ∈ D.host.AA⁻¹, Valued.v (t z) = 1

structure IsStageGeo (ψ : AddChar (AF D.host.F) ℂ) {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (FA : Fr A) (FA' : Fr A')
    (FW : Fr WW) (hr : A.rank + A'.rank = WW.rank) (Bs : Base D.host.F D.host.E) (Γ : Geo D.sp.cm.sig A.rank A'.rank) : Prop where

  pairA : IsPair ψ true A WW (finCongr hr) Bs Γ.V Γ.W Γ.M

  pairB : IsPair ψ false A' WW (finCongr hr) Bs Γ.V' Γ.W Γ.M'

  latA : IsLat (finCongr hr) Γ.V Γ.W X.rA.Λ X.rW.Λ

  latB : IsLat (finCongr hr) Γ.V' Γ.W X.rA'.Λ X.rW.Λ

  cartA : IsCart true FA FW (finCongr hr) Bs Γ.V Γ.W

  cartB : IsCart false FA' FW (finCongr hr) Bs Γ.V' Γ.W

  JA : Γ.V.J = (1 : D.host.E) • A.gram

  JB : Γ.V'.J = (-1 : D.host.E) • A'.gram

  measA : Γ.M.μ = X.m.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A 1 JA)

  domA : Γ.M.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A 1 JA '' X.fd

  measB : Γ.M'.μ = X.m'.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A' (-1) JB)

  domB : Γ.M'.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A' (-1) JB '' X.fd'

  basA : ∀ v : Bs.P, ((Γ.V.bas v)⁻¹).1 = -(A.gram.map (Bs.τ v) * X.rA.β.1.map (evW (Bs.τ v)))ᵀ

  basB : ∀ v : Bs.P, ((Γ.V'.bas v)⁻¹).1 = (A'.gram.map (Bs.τ v) * X.rA'.β.1.map (evW (Bs.τ v)))ᵀ

  basW : ∀ v : Bs.P, AUnit (Bs.τ v) →
    (Γ.W.bas v).1 = (X.rW.β.1.map (evW (Bs.τ v))).submatrix (finCongr hr) (finCongr hr)

end GlobalTheory.StageGeo

end
