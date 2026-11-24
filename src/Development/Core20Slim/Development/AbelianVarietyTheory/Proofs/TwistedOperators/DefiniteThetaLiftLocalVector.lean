module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonvanishingFiniteDatumDefiniteLift
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.AdjVecLocal

variable {D : D7}

section Pure

variable {v : FinPl D} {k : Type} [CommRing k] {n a t : ℕ}





variable (r : v.adicCompletionIntegers D.host.F →+* k)
  (hr : ∀ x : v.adicCompletionIntegers D.host.F, r x = 0 ↔ Valued.v (x : Fv D.host.F v) < 1)
include hr










end Pure

section Local







variable (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))

theorem frMapAdj_smul (e : AE D) (x : WO S T) :
    frMapAdj S T βS βT (cA D e • x) = toEAf D e • frMapAdj S T βS βT x := by
  have h : (((cA D e • x).map (toEAf D)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
      toEAf D e • ((x.map (toEAf D)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ := Matrix.ext fun i j => by
    change GlobalTheory.AdelicLatMove.cF D (toEAf D (cA D e * x j i)) = toEAf D e * GlobalTheory.AdelicLatMove.cF D (toEAf D (x j i))
    rw [RingHom.map_mul, RingHom.map_mul, GlobalTheory.AdelicLatMove.toEAf_cA, GlobalTheory.PlaceVec.cF_cF_toEAf]
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.frMapAdj_eq, h, Matrix.mul_smul, Matrix.smul_mul]

theorem frMapAdj_half {e : AE D} {x : WO S T} (hx : IsHalf (cA D e) x) (i : Fin S.rank) (j : Fin T.rank) :
    toEAf D e * frMapAdj S T βS βT x i j = frMapAdj S T βS βT x i j := by
  have h : cA D e • x = x := Matrix.ext hx
  have := frMapAdj_smul S T βS βT e x
  rw [h] at this
  exact (congrFun (congrFun this i) j).symm












end Local



end GlobalTheory.AdjVecLocal

end
