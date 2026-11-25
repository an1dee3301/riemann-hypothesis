module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion

variable {D : D7}

def TrivOnF (D : D7) (ξ : (AE D)ˣ →* Circle) : Prop := ∀ a : (AF D.host.F)ˣ, ξ (idF D a) = 1

def IsTildeDet (V : HSp D) (ξ : (AE D)ˣ →* Circle) (g : GA D V) (c : Circle) : Prop :=
  (∃ x, IsDetRoot V g x) ∧ ∀ x, IsDetRoot V g x → ξ x = c

def WeilDatumUnique (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS χT om' →
      ∀ (g : GA D S) (h : GA D T) (f : WO S T → ℂ), IsThetaFunO ψ S T f → om' (g, h) f = om (g, h) f

def WeilDatumTwist (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT ξ ξ' : (AE D)ˣ →* Circle)
    (om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    TrivOnF D ξ → TrivOnF D ξ' →
    IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T (χS * ξ) (χT * ξ') om' →
      ∀ (g : GA D S) (h : GA D T), ∃ a b : Circle, IsTildeDet S ξ' g a ∧ IsTildeDet T ξ h b ∧
        ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
          om' (g, h) f = ((a⁻¹ * b : Circle) : ℂ) • om (g, h) f

def WeilDatumDetermined (D : D7) : Prop := WeilDatumUnique D ∧ WeilDatumTwist D

theorem IsTildeDet.at_one {V : HSp D} {ξ : (AE D)ˣ →* Circle} {c : Circle} (h : IsTildeDet V ξ 1 c) : c = 1 := by
  have h1 : IsDetRoot V 1 1 := by simp [IsDetRoot]
  rw [← h.2 1 h1, map_one]

theorem WeilDatumTwist.unique (H : WeilDatumTwist D) : WeilDatumUnique D := by
  intro ψ S T χS χT om om' h h' g k f hf
  obtain ⟨a, b, ha, hb, e⟩ := H ψ S T χS χT 1 1 om om' (fun _ => rfl) (fun _ => rfl) h
    (by simpa using h') g k
  obtain ⟨x, hx⟩ := ha.1
  obtain ⟨y, hy⟩ := hb.1
  have ha1 : a = 1 := (ha.2 x hx).symm
  have hb1 : b = 1 := (hb.2 y hy).symm
  simpa [ha1, hb1] using e f hf

end GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion

end
