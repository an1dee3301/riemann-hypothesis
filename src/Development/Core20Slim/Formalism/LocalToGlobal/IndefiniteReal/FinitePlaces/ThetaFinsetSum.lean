module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
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
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
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
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem dRhoStable (D : D7) : DRhoStable D := by
  intro ψ θ hψ hθ S T τ z f hf
  exact (Formalism.IndefR.Fock.DRho.thetaDRho D ψ θ hψ hθ (Formalism.IndefR.Eqv.lineAtExists_holds D) S T τ z f hf).1

section Pt

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

lemma theta_sub {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f - g) := by
  convert Formalism.IndefR.Fock.CCR.theta_add_smul hf hg (-1) using 1 <;>
    ext x <;> simp [sub_eq_add_neg]

lemma theta_finsetSum {ι : Type*} (s : Finset ι) (g : ι → WO S T → ℂ) (hg : ∀ i ∈ s, IsThetaFunO ψ S T (g i)) :
    IsThetaFunO ψ S T (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Formalism.IndefR.Fock.CCR.theta_zero ψ S T
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Formalism.IndefR.Fock.CCR.theta_add (hg a (Finset.mem_insert_self a s))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

lemma theta_opPow {ι : Type} (A : ι → (WO S T → ℂ) → (WO S T → ℂ))
    (hA : ∀ i g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (A i g)) (k : ι →₀ ℕ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (opPow A k f) := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => exact hf
  | cons i l ih => exact hA i _ ih

theorem ptStable (D : D7) : PtStable D := by
  intro ψ θ hψ hθ S T sS sT BS BT f P hf
  have hA : ∀ (i : FVar D T.rank S.rank) (g : WO S T → ℂ), IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) := by
    intro i g hg
    unfold aPlusAll aPlus crea
    exact Formalism.IndefR.Fock.CCR.theta_smul
      (theta_sub (dRhoStable D ψ θ hψ hθ S T i.1 _ g hg)
        (Formalism.IndefR.Fock.CCR.theta_smul (dRhoStable D ψ θ hψ hθ S T i.1 _ g hg) _)) _
  unfold pureTensorO pureTensorL
  rw [Module.Basis.constr_apply, Finsupp.sum]
  exact theta_finsetSum _ _ fun k _ =>
    Formalism.IndefR.Fock.CCR.theta_smul (theta_opPow _ hA k hf) _

end Pt

end Formalism.IndefR.Fin
