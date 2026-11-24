module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotMove

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7} {T : Type} {A A' WW : HSp D}

def moveTri (Y : Tri T A A' WW) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E))
    (g : GA D A) (g' : GA D A') (h : GA D WW) (t₀ : T) (r r' : T → ℂ) : Tri T A A' WW where
  rA := ⟨ΛA, Lev.finE A g * Y.rA.β, Y.rA.s, Y.rA.B⟩
  rA' := ⟨ΛA', Lev.finE A' g' * Y.rA'.β, Y.rA'.s, Y.rA'.B⟩
  rW := ⟨ΛW, Lev.finE WW h * Y.rW.β, Y.rW.s, Y.rW.B⟩
  ω := Y.ω
  ω' := Y.ω'
  vac := Y.ω t₀ (g, h) Y.vac
  vac' := Y.ω' t₀ (g', h) Y.vac'
  e := Y.e
  c := Y.c
  f t := (r t)⁻¹ • Y.ω t (g, h) (Y.f t)
  f' t := (r' t)⁻¹ • Y.ω' t (g', h) (Y.f' t)
  m := Y.m.map (fun x => x * g⁻¹)
  fd := (fun x => x * g) ⁻¹' Y.fd
  m' := Y.m'.map (fun x => x * g'⁻¹)
  fd' := (fun x => x * g') ⁻¹' Y.fd'

variable (Y : Tri T A A' WW) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
  (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E))
  (g : GA D A) (g' : GA D A') (h : GA D WW) (t₀ : T) (r r' : T → ℂ)

end GlobalTheory.BotMove

end
