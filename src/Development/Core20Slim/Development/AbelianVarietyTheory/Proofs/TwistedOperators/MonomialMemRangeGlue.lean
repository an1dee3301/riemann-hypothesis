module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

namespace GlobalTheory.MonomialRangeMembership

open MvPolynomial

theorem monomial_mem_range_glue {D : Formalism.BasicNotions.D7} {a b : ℕ}
    (m : Formalism.IndefR.Datum.FVar D b a →₀ ℕ) :
    (monomial m (1 : ℂ) : Formalism.IndefR.Links.PolF D b a) ∈
      Set.range (GlobalTheory.Chain.RealIt.glue (D := D) (a := a) (b := b)) := by
  refine ⟨fun τ => ∏ s : Fin b × Fin a, X s ^ m (τ, s), ?_⟩
  rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_prod_type]
  unfold GlobalTheory.Chain.RealIt.glue
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [map_prod, map_pow, rename_X]

theorem span_range_glue : ∀ {D : Formalism.BasicNotions.D7} {a b : Nat}, @Eq (@Submodule Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing)) (@Submodule.span Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing) (@Set.range (Formalism.IndefR.Links.PolF D b a) (@Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.R D) (Formalism.BasicNotions.D7.what₂ D) → GlobalTheory.Chain.RealIt.LPol b a) (@GlobalTheory.Chain.RealIt.glue D a b))) (@Top.top (@Submodule Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing)) (@Submodule.instTop Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing))) := by
  intro D a b
  rw [eq_top_iff, ← (basisMonomials (Formalism.IndefR.Datum.FVar D b a) ℂ).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨m, rfl⟩
  rw [coe_basisMonomials]
  exact monomial_mem_range_glue m

end GlobalTheory.MonomialRangeMembership
