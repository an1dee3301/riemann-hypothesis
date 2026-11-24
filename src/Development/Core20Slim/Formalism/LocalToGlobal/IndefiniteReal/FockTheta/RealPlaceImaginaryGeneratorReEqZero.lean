module

public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped ComplexOrder

namespace Formalism.IndefR.Fock.CCR

open Formalism.IndefR.Fock.Sk

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem realPlace_imaginaryGenerator_re_eq_zero (D : D7) (τ : D.what₂.Tau) : (tauE D τ D.host.xi0).re = 0 := by
  simp [Formalism.BasicNotions.Host.xi0, map_div₀, map_neg, map_one, map_mul, map_natCast, Formalism.L2.Theta.tauE_sqrtMinusD,
    Complex.div_re]


theorem heisO_add_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (c : ℂ) (f g : WO S T → ℂ) :
    heisO ψ S T u (f + c • g) = heisO ψ S T u f + c • heisO ψ S T u g := by

  funext w
  simp only [heisO, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem theta_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T 0 := {
  quasi := by intro γ w; simp
  level := ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun u _ _ => by funext w; simp [heisO]⟩
  cont := continuous_const
  smooth := fun _ _ _ _ _ => contDiff_const }

theorem theta_add_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hg : IsThetaFunO ψ S T g) (c : ℂ) : IsThetaFunO ψ S T (f + c • g) := {
  quasi := by
    intro γ w
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hf.quasi, hg.quasi]
    ring
  level := by
    obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨V, hV, hVg⟩ := hg.level
    refine ⟨U ⊓ V, by rw [AddSubgroup.coe_inf]; exact hU.inter hV, fun u hu hinf => ?_⟩
    rw [heisO_add_smul, hUf u hu.1 hinf, hVg u hu.2 hinf]
  cont := hf.cont.add (hg.cont.const_smul c)
  smooth := by
    intro k L hL hfin w
    simpa [Pi.add_apply, Pi.smul_apply] using
      (hf.smooth k L hL hfin w).add ((hg.smooth k L hL hfin w).const_smul c) }

theorem theta_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) (c : ℂ) :
    IsThetaFunO ψ S T (c • g) := by
  have h := theta_add_smul (theta_zero ψ S T) hg c
  simpa using h

theorem theta_add {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (f + g) := by
  have h := theta_add_smul hf hg 1
  simpa using h

theorem theta_function_linear_combination {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hg : IsThetaFunO ψ S T g) (a b : ℂ) : IsThetaFunO ψ S T (a • f + b • g) := theta_add (theta_smul hf a) (theta_smul hg b)

section Assembly

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

end Assembly

section Main

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}



end Main

end Formalism.IndefR.Fock.CCR

end
