module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Multiset.ZeroCons
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField
open GlobalTheory.Chain
open GlobalTheory.Ker (ipO)

namespace GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

def creOp (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (l : FVar D W.rank V.rank) (g : WO V W → ℂ) : WO V W → ℂ :=
  aPlusAll (heisO ψ V W) θ (fun τ => cplxO (cart M τ) (cart M' τ)) (onb M) (onb M') l g

def annOp (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (l : FVar D W.rank V.rank) (g : WO V W → ℂ) : WO V W → ℂ :=
  (-(fockScale D l.1 : ℂ)⁻¹) •
    annih (heisO ψ V W) θ l.1 (cplxO (cart M l.1) (cart M' l.1)) (unitMap (onb M l.1) (onb M' l.1) l.2.1 l.2.2) g

def multiFact {ι : Type} (α : ι →₀ ℕ) : ℕ := α.prod fun _ k => k.factorial


open Classical in
def FockLaws (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (f : WO V W → ℂ) : Prop :=
  (∀ P : PolF D W.rank V.rank, IsThetaFunO ψ V W (ptOf ψ θ M M' f P)) ∧
  (∀ (l l' : FVar D W.rank V.rank) (g : WO V W → ℂ), IsThetaFunO ψ V W g →
    creOp ψ θ M M' l (creOp ψ θ M M' l' g) = creOp ψ θ M M' l' (creOp ψ θ M M' l g)) ∧
  (∀ (l l' : FVar D W.rank V.rank) (g : WO V W → ℂ), IsThetaFunO ψ V W g →
    annOp ψ θ M M' l (creOp ψ θ M M' l' g) - creOp ψ θ M M' l' (annOp ψ θ M M' l g) = if l = l' then g else 0) ∧
  (∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratL W V) 𝓕 μ → ∀ α β : FVar D W.rank V.rank →₀ ℕ,
      ipO μ 𝓕 (ptOf ψ θ M M' f (MvPolynomial.monomial α 1)) (ptOf ψ θ M M' f (MvPolynomial.monomial β 1)) =
        if α = β then (multiFact α : ℂ) * ipO μ 𝓕 f f else 0) ∧
  Function.Injective (ptOf ψ θ M M' f)

def VacuumFock (D : D7) : Prop :=
  ∀ (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S')
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ f : WO V W → ℂ, IsVacVec ψ θ M M' f → FockLaws ψ θ M M' f

theorem ptOf_one (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (f : WO V W → ℂ) : ptOf ψ θ M M' f 1 = f := by
  have h : (1 : PolF D W.rank V.rank) = MvPolynomial.basisMonomials _ ℂ 0 := by simp
  unfold ptOf pureTensorO pureTensorL
  rw [h, Module.Basis.constr_basis]
  simp [opPow]

end GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors

end
