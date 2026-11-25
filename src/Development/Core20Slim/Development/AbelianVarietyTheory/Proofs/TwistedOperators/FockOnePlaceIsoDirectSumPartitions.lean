module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqRepTopVecOfUnitriangular
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.DFinsupp.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

theorem iso_directSum_fockOne : ∀ (a b : ℕ) (α β : ℤ), Iso (Representation.directSum fun i : GlobalTheory.GLDuality.Part (min a b) => Representation.tprod ((twist (detU a ^ α) ((irr a (GlobalTheory.GLDuality.pad a i)).comp (conjU a))).comp (MonoidHom.fst (U a) (U b))) ((twist (detU b ^ β) (irr b (GlobalTheory.GLDuality.pad b i))).comp (MonoidHom.snd (U a) (U b)))) (fockOne a b α β) := by
  intro a b α β
  obtain ⟨e⟩ := GlobalTheory.GLDuality.nonempty_equiv_polyRep a b
  obtain ⟨e, he⟩ := Iso.of_equiv e
  refine ⟨e, fun p x => ?_⟩
  have key : (Representation.directSum fun i : GlobalTheory.GLDuality.Part (min a b) => Representation.tprod
      ((twist (detU a ^ α) ((irr a (GlobalTheory.GLDuality.pad a i)).comp (conjU a))).comp (MonoidHom.fst (U a) (U b)))
      ((twist (detU b ^ β) (irr b (GlobalTheory.GLDuality.pad b i))).comp (MonoidHom.snd (U a) (U b)))) p x =
      ((((detU a ^ α) p.1 * (detU b ^ β) p.2 : ℂˣ) : ℂ)) •
      (Representation.directSum fun i : GlobalTheory.GLDuality.Part (min a b) =>
        GlobalTheory.GLDuality.pieceRep (MonoidHom.id (GL (Fin a) ℂ)) (MonoidHom.id (GL (Fin b) ℂ)) i)
        (unitaryIncl a (conjU a p.1), unitaryIncl b p.2) x := by
    apply DFinsupp.ext
    intro i
    change TensorProduct.map ((((detU a ^ α) p.1 : ℂˣ) : ℂ) • (irr a (GlobalTheory.GLDuality.pad a i) (conjU a p.1)))
        ((((detU b ^ β) p.2 : ℂˣ) : ℂ) • (irr b (GlobalTheory.GLDuality.pad b i) p.2)) (x i) =
      ((((detU a ^ α) p.1 * (detU b ^ β) p.2 : ℂˣ) : ℂ)) •
        TensorProduct.map (irr a (GlobalTheory.GLDuality.pad a i) (conjU a p.1)) (irr b (GlobalTheory.GLDuality.pad b i) p.2) (x i)
    rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_smul, Units.val_mul, LinearMap.smul_apply]
  rw [key, map_smul, he]
  rfl

end GlobalTheory.OneFunctional
