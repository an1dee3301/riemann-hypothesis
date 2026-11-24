module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColMapEqColMapV
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.KerDiag
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FockTranslate

theorem compAt_fin {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) {V : HSp D} (g : GA D V) (hg : g ∈ Formalism.L2.Theta.GfC V) :
    Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  have h6 : (Formalism.L2.Theta.mt V g).map (Formalism.L2.Theta.infPart D) = 1 :=
    congrArg Units.val (show Formalism.L2.Theta.infHom V g = 1 from hg)
  unfold Formalism.IndefR.Datum.compAt
  rw [show (Formalism.L2.Theta.mt V g).map (fun a => θ τ (Formalism.L2.Theta.infPart D a)) =
    ((Formalism.L2.Theta.mt V g).map (Formalism.L2.Theta.infPart D)).map (θ τ) from (Matrix.map_map).symm, h6]
  exact Matrix.map_one _ (θ τ).map_zero (θ τ).map_one

theorem fockComp_translate : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : VertexFrames G) (t : T) (j : ℕ),
    j + 1 ≤ D.R.m → ∀ (f : WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ),
    IsThetaFunO W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) f →
    ∀ (a k₁ : FinPt G (.top j)) (b k₂ : FinPt G (.top (j + 1))),
      fockComp W B (.top t j) f (a * k₁) (b * k₂) =
        fockComp W B (.top t j) (W.om (.top t j) ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1))))) f) a b := by
  intro D T L sc G W B t j hj f hf a k₁ b k₂
  have hom := W.om_is (.top t j) hj
  have hcomm : ∀ P, W.om (.top t j) ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1)))))
      (fockIn W B (.top t j) f P) = fockIn W B (.top t j) (W.om (.top t j) ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1))))) f) P := by
    intro P
    unfold fockIn
    refine Formalism.IndefR.Eqv.KerDiag.comm_pureTensorO W.ψ_std W.θ W.θ_is _ _ _ _ _ (fun τ z g hg => ?_) hf P
    rw [GlobalTheory.OrientedHeis.om_dRho hom W.θ_is _ _ τ z hg, compAt_fin W.θ τ _ k₂.2, compAt_fin W.θ τ _ (inv_mem k₁.2),
      Matrix.one_mul, Matrix.mul_one]
  unfold fockComp
  congr 1
  funext M
  unfold jetTab kerFin GridData.Weil.ker
  simp only [GridData.toPair, thetaKO, Subgroup.coe_mul]
  rw [show ((a : GA D (G.V (.top j))) * k₁, (b : GA D (G.V (.top (j + 1)))) * k₂) =
    ((a : GA D (G.V (.top j))), (b : GA D (G.V (.top (j + 1))))) * ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1))))) from rfl,
    map_mul, Module.End.mul_apply, hcomm]

end GlobalTheory.FockTranslate

end
