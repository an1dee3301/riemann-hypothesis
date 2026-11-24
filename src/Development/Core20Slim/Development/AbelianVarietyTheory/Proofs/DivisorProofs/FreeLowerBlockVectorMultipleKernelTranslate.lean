module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointHalfDatumStabilizerPairMove
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitEmbeddingValuedEqIntValuationInteger
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowLocKMulInf
public import Development.Core20Slim.Formalism.LocalToGlobal.UnitaryNorms.CharProd
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
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
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies 
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open  GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.FreeBlockTwist

section Away

def UnitAway (p : ℕ) {K : Type} [Field K] (z : K) : Prop :=
  z ≠ 0 ∧ ∃ m : ℕ, IsIntegral ℤ ((p : K) ^ m * z) ∧ IsIntegral ℤ ((p : K) ^ m * z⁻¹)

variable {p : ℕ} {K : Type} [Field K]










theorem UnitAway.map {L : Type} [Field L] (f : K →+* L) {z : K} (h : UnitAway p z) : UnitAway p (f z) := by
  obtain ⟨h0, m, h1, h2⟩ := h
  refine ⟨by simpa using h0, m, ?_, ?_⟩
  · simpa using map_isIntegral_int f h1
  · simpa using map_isIntegral_int f h2






end Away

section Lattice

open GlobalTheory.StdFrames (cpt OA)





variable {D : D7}



variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]




end Lattice

section Datum

open GlobalTheory.StdFrames (cpt OA)

variable {D : D7}


variable {Q : Finset (Pl D.host.E)} {ν : Datum.EAf D}
  (h1 : ∀ PP ∈ Q, Valued.v (cpt PP ν) = WithZero.exp (-1 : ℤ)) (h2 : ∀ PP, PP ∉ Q → cpt PP ν = 1)







variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



end Datum

section Element


variable {D : D7}


theorem exists_adapted_frame_with_unit_scaling {R : Type} [CommRing R] {n : ℕ} (β : GL (Fin n) R) (K : Matrix (Fin n) (Fin n) R) :
    (β⁻¹).1 * K = (β⁻¹).1 * K * β.1 * (β⁻¹).1 := by
  rw [Matrix.mul_assoc _ β.1, Units.mul_inv, Matrix.mul_one]

theorem map_one_mul_eq_mul_one {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) {n : ℕ} (γ : Matrix (Fin n) (Fin n) R)
    {K : Matrix (Fin n) (Fin n) A} (h : K = 1) : K.map f * γ = γ * 1 := by
  rw [h, Matrix.map_one _ (map_zero f) (map_one f), Matrix.mul_one, Matrix.one_mul]

theorem frMapAdj_actO_one (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D))
    (g : GA D S) (x : WO S T) : frMapAdj S T βS βT (actO S T g 1 x) =
      (βS⁻¹).1 * (Formalism.L2.Theta.mt S g).map (toEAf D) * βS.1 * frMapAdj S T βS βT x :=
  (GlobalTheory.AdjDatumMove.adj_frame_move (cA D) (toEAf D) _ _ _ _ _ _ x _ _ _ _ (GlobalTheory.AdjDatumMove.gram_inv_mul S g)
    (GlobalTheory.AdelicLatMove.gram_mul_inv T 1) (exists_adapted_frame_with_unit_scaling βS _)
    (map_one_mul_eq_mul_one (toEAf D) βT.1 ((congrArg (Formalism.L2.Theta.mt T) inv_one).trans (GlobalTheory.IdemSupport.mt_one T)))).trans
    (Matrix.mul_one _)


end Element

section Scalar

variable {D : D7}










end Scalar




end GlobalTheory.FreeBlockTwist

end
