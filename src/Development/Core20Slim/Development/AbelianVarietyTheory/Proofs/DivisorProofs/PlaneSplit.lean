module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepK

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Geo Plane Chars RealMaps IsMatched IsConst)

variable {D : D7}

def InLat (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (z : V.V) : Prop := V.frame.equivFun z ∈ Λ

def PlaneSplit (S S₁ : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V) : Prop :=
  S.rank = S₁.rank + 2 ∧ Formalism.BasicNotions.HSpace.IsIsomEmb S₁ S ι ∧ S.hD x x = 0 ∧ S.hD y y = 0 ∧ S.hD x y = 1 ∧
    (∀ u, S.hD (ι u) x = 0 ∧ S.hD (ι u) y = 0) ∧ (∀ u, InLat S₁ Λ₁ u ↔ InLat S Λ (ι u)) ∧
    ∀ z, InLat S Λ z → ∃ (s r : D.host.E) (u : S₁.V), InLat S Λ (s • x) ∧ InLat S Λ (r • y) ∧ InLat S₁ Λ₁ u ∧
      z = s • x + ι u + r • y

def IsStepB {T : Type} {A A' WW B' WW₁ : HSp D} (X : Tri T A A' WW) (Y : Tri T A B' WW₁) : Prop :=
  Y.rA = X.rA ∧ (∃ ι x y, PlaneSplit A' B' X.rA'.Λ Y.rA'.Λ ι x y) ∧ ∃ ι x y, PlaneSplit WW WW₁ X.rW.Λ Y.rW.Λ ι x y

def HasConstR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {a a' : ℕ} (Γ : Geo σ a a') (R : RealMaps F a a') (χ : Chars F E) (κ : ℂ) : Prop :=
  ∃ om om' Rf, IsMatched B Γ χ om om' R Rf ∧ IsConst B Γ χ om om' R Rf κ

end GlobalTheory.SqStepK
