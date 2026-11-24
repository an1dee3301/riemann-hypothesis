module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.LocalRingCardinality.DataTies
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumCharacterPositiveDefiniteSourceStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
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
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompactAction


theorem isCartanInv_one {n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} (h : Bᴴ * G * B = 1) : IsCartanInv G 1 := by
  have hB : B * (Bᴴ * G) = 1 := mul_eq_one_comm.1 h
  have hi : B⁻¹ = Bᴴ * G := Matrix.inv_eq_right_inv hB
  have hu : IsUnit B := IsUnit.of_mul_eq_one _ hB
  have hG : G = (B⁻¹)ᴴ * B⁻¹ := by
    have h1 : (B⁻¹)ᴴ * Bᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hi, hB, Matrix.conjTranspose_one]
    calc G = ((B⁻¹)ᴴ * Bᴴ) * G := by rw [h1, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, ← hi]
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  refine Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit ?_)
  exact (Matrix.isUnit_nonsing_inv_iff).2 hu



theorem pureTensorO_smul {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (c : ℂ) (f : WO S T → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (c • f) P = c • pureTensorO ψ θ S T sS sT BS BT f P := by
  have hd : ∀ τ z (f : WO S T → ℂ), dRho (heisO ψ S T) θ τ z (c • f) = c • dRho (heisO ψ S T) θ τ z f := by
    intro τ z f
    funext x
    simp only [Formalism.IndefR.Datum.dRho, heisO, Pi.smul_apply, smul_eq_mul]
    rw [← deriv_const_mul_field]
    congr 1
    funext t
    ring
  refine (GlobalTheory.OrientedHeis.pureTensorL_intertwine (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) _ _ (c • (1 : Module.End ℂ (WO S T → ℂ))) (fun k f _ => ⟨trivial, ?_⟩) f trivial P).2.symm
  simp only [aPlusAll, Formalism.IndefR.Datum.aPlus, crea, LinearMap.smul_apply, Module.End.one_apply, hd]
  rw [smul_comm Complex.I c, ← smul_sub, smul_comm]


end GlobalTheory.FockCompactAction

end
