module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
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
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoordDenom

theorem finCoord_mul_denom : ∀ (D : D7), ∃ c : ℕ, 0 < c ∧ ∀ (e₁ e₂ : ℕ) (a b : Af D.host.F ⊗[D.host.F] D.host.E), (∀ k, (e₁ : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D a k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) → (∀ k, (e₂ : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D b k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) → ∀ k, ((c * e₁ * e₂ : ℕ) : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (a * b) k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := by
  intro D
  set B := Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E) with hB
  obtain ⟨c, hc, h⟩ := GlobalTheory.HolDict.ShortVec.exists_common_denom (GlobalTheory.HolDict.ShortVec.intRing D.host.F)
    (fun p : Fin (Module.finrank D.host.F D.host.E) × Fin (Module.finrank D.host.F D.host.E) ×
      Fin (Module.finrank D.host.F D.host.E) => B.repr (B p.1 * B p.2.1) p.2.2)
    fun _ => GlobalTheory.HolDict.ShortVec.exists_denom_adele _
  refine ⟨c, hc, fun e₁ e₂ a b ha hb k => ?_⟩
  have ha' : ∀ i, (e₁ : Af D.host.F) * B.repr a i ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := ha
  have hb' : ∀ i, (e₂ : Af D.host.F) * B.repr b i ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := hb
  change ((c * e₁ * e₂ : ℕ) : Af D.host.F) * B.repr (a * b) k ∈ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← B.sum_repr a, ← B.sum_repr b, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Subring.sum_mem _ fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have e : ((c * e₁ * e₂ : ℕ) : Af D.host.F) * (B.repr a i * B.repr b j * B.repr (B i * B j) k) =
      ((e₁ : Af D.host.F) * B.repr a i) * ((e₂ : Af D.host.F) * B.repr b j) * ((c : Af D.host.F) * B.repr (B i * B j) k) := by
    push_cast; ring
  rw [e]
  exact Subring.mul_mem _ (Subring.mul_mem _ (ha' i) (hb' j)) (h (i, j, k))

end GlobalTheory.CoordDenom
