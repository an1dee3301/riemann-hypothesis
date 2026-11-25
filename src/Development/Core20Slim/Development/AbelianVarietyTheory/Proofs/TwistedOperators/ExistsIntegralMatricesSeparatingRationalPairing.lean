module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Batteries.Classes.RatCast
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatPairSep

variable {D : D7}

theorem eq_zero_of_trace_integralBasis (D : D7) (q : D.host.E)
    (h : ∀ k, Algebra.trace ℚ D.host.E (q * integralBasis D.host.E k) = 0) : q = 0 := by
  refine (traceForm_nondegenerate ℚ D.host.E).1 q fun z => ?_
  have hl : (Algebra.traceForm ℚ D.host.E) q = 0 :=
    (integralBasis D.host.E).ext fun k => by
      rw [LinearMap.zero_apply, Algebra.traceForm_apply]; exact h k
  rw [hl, LinearMap.zero_apply]

theorem pairQ_sub (W : HSp D) {r : ℕ} (y y' : Matrix (Fin W.rank) (Fin r) D.host.E) :
    pairQ W y - pairQ W y' = pairQ W (y - y') := by
  have : adj D (y - y') = adj D y - adj D y' := by
    ext i j; simp [adj, Formalism.UG.cT]
  simp only [pairQ, this, Matrix.sub_mul, smul_sub]

theorem eq_of_pairQ_eq (W : HSp D) {r : ℕ} (y y' : Matrix (Fin W.rank) (Fin r) D.host.E)
    (h : pairQ W y = pairQ W y') : y = y' := by
  have h1 : adj D y * W.gram = adj D y' * W.gram := by
    have := congrArg (fun M => (D.host.xi0)⁻¹ • M) h
    simpa [pairQ, smul_smul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)] using this
  have h2 : adj D y = adj D y' := by
    have := congrArg (fun M => M * W.gram⁻¹) h1
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit W)] using this
  refine Matrix.ext fun i j => ?_
  have := congrFun (congrFun h2 j) i
  simp only [adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
  exact (D.sp.cm.sig : D.host.E →+* D.host.E).injective this

theorem exists_sep (D : D7) (W : HSp D) (r : ℕ) :
    ∃ (n : ℕ) (X : Fin n → Matrix (Fin W.rank) (Fin r) D.host.E), (∀ j a b, IsIntegral ℤ (X j a b)) ∧
      ∀ y y' : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ j, ratPair W y (X j) = ratPair W y' (X j)) → y = y' := by
  let ι := Fin W.rank × Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)
  let e := Fintype.equivFin ι
  let Y : ι → Matrix (Fin W.rank) (Fin r) D.host.E := fun t => Matrix.single t.1 t.2.1 (integralBasis D.host.E t.2.2)
  refine ⟨Fintype.card ι, fun j => Y (e.symm j), ?_, ?_⟩
  · intro j a b
    simp only [Y, Matrix.single_apply]
    split_ifs
    · rw [integralBasis_apply]; exact (RingOfIntegers.basis D.host.E _).isIntegral_coe
    · exact isIntegral_zero
  · intro y y' h
    apply eq_of_pairQ_eq W y y'
    rw [← sub_eq_zero, pairQ_sub]
    refine Matrix.ext fun l i => ?_
    rw [Matrix.zero_apply]
    refine eq_zero_of_trace_integralBasis D _ fun k => ?_
    have hj := h (e (i, l, k))
    simp only [ratPair, Equiv.symm_apply_apply, Y, Rat.cast_inj] at hj
    rw [← sub_eq_zero, ← map_sub, ← Matrix.trace_sub, ← Matrix.sub_mul, pairQ_sub,
      Matrix.trace_mul_single] at hj
    simpa [MulOpposite.smul_eq_mul_unop] using hj

end GlobalTheory.RatPairSep

theorem GlobalTheory.RatPairSep.main : ∀ (D : D7) (W : HSp D) (r : ℕ), ∃ (n : ℕ) (X : Fin n → Matrix (Fin W.rank) (Fin r) D.host.E),
    (∀ j a b, IsIntegral ℤ (X j a b)) ∧ ∀ y y' : Matrix (Fin W.rank) (Fin r) D.host.E,
    (∀ j, ratPair W y (X j) = ratPair W y' (X j)) → y = y' := GlobalTheory.RatPairSep.exists_sep
