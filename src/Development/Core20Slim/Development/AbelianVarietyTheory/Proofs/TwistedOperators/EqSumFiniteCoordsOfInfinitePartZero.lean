module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Prod
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InfZeroFinSum

open Module

theorem repr_map_id {F A A' E ι : Type*} [Field F] [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A']
    [CommRing E] [Algebra F E] [Fintype ι] [DecidableEq ι] (b : Basis ι F E) (f : A →ₐ[F] A')
    (z : A ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis A' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) z) k
      = f ((Algebra.TensorProduct.basis A b).repr z k) := by
  have hz : z = ∑ i, (Algebra.TensorProduct.basis A b).repr z i • (Algebra.TensorProduct.basis A b) i :=
    ((Algebra.TensorProduct.basis A b).sum_repr z).symm
  have hm : Algebra.TensorProduct.map f (AlgHom.id F E) z
      = ∑ i, f ((Algebra.TensorProduct.basis A b).repr z i) • (Algebra.TensorProduct.basis A' b) i := by
    conv_lhs => rw [hz]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rw [hm, (Algebra.TensorProduct.basis A' b).repr_sum_self]

theorem eq_sum_of_fst_zero {F Ai Afn E ι : Type*} [Field F] [CommRing Ai] [Algebra F Ai] [CommRing Afn]
    [Algebra F Afn] [CommRing E] [Algebra F E] [Fintype ι] [DecidableEq ι] (b : Basis ι F E)
    (z : (Ai × Afn) ⊗[F] E)
    (hz : Algebra.TensorProduct.map (AlgHom.fst F Ai Afn) (AlgHom.id F E) z = 0) :
    z = ∑ k, ((0 : Ai), (Algebra.TensorProduct.basis Afn b).repr
      (Algebra.TensorProduct.map (AlgHom.snd F Ai Afn) (AlgHom.id F E) z) k) ⊗ₜ[F] b k := by
  have h1 : ∀ k, ((Algebra.TensorProduct.basis (Ai × Afn) b).repr z k).1 = 0 := by
    intro k
    have := repr_map_id b (AlgHom.fst F Ai Afn) z k
    rw [hz, map_zero] at this
    simpa using this.symm
  conv_lhs => rw [← (Algebra.TensorProduct.basis (Ai × Afn) b).sum_repr z]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [repr_map_id b (AlgHom.snd F Ai Afn) z k]
  have hc : (Algebra.TensorProduct.basis (Ai × Afn) b).repr z k
      = ((0 : Ai), AlgHom.snd F Ai Afn ((Algebra.TensorProduct.basis (Ai × Afn) b).repr z k)) :=
    Prod.ext (h1 k) rfl
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact congrArg (fun x => x ⊗ₜ[F] b k) hc

end GlobalTheory.InfZeroFinSum

theorem GlobalTheory.InfZeroFinSum.eq_sum_finCoord_of_infPart_eq_zero : ∀ (D : D7) (z : AE D), infPart D z = 0 → z = ∑ k, pairA D.host.F 0 (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (GlobalTheory.HolDict.ShortVec.finPr D z) k) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k := by
  intro D z hz
  exact GlobalTheory.InfZeroFinSum.eq_sum_of_fst_zero (Module.finBasis D.host.F D.host.E) z hz
