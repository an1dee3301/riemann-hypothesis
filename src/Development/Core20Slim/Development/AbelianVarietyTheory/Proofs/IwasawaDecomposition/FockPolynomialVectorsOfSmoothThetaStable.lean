module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Pi.Basic
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
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

namespace GlobalTheory.FockTheta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ptStable : ∀ D : D7, Formalism.IndefR.Fin.PtStable D := by
  intro D ψ θ hψ hθ S T sS sT BS BT f P hf
  exact (GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
    (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun c _ => GlobalTheory.OrientedHeis.theta_smul c) _
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) 1
    (fun k _ hg => ⟨GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_sub
      (GlobalTheory.OrientedHeis.theta_dRho hθ hψ k.1 _ hg)
      (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ k.1 _ hg))), rfl⟩) f hf P).1

end GlobalTheory.FockTheta

end
