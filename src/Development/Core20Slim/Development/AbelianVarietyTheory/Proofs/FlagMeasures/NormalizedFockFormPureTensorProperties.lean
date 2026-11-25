module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.GradedWeylDivisibility.StatementD
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.Columns.PolyFn
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
public import Formalism.RealPlaceAnalysis.FockPairGl
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.FunLike.Fintype
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.FockTen

theorem fockF_eq_fockL {σ : Type} (f g : MvPolynomial σ ℂ) : Formalism.REAL.fockF f g = Formalism.L2.DIV.fockL g f := by
  classical
  rw [Formalism.L2.DIV.fockL_apply,
    Formalism.L2.DIV.fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  unfold Formalism.REAL.fockF
  rw [Finset.sum_subset (Finset.subset_union_left : f.support ⊆ f.support ∪ g.support)]
  · refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Formalism.L2.DIV.mfact]
    ring
  · intro m _ hm
    have hf : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
    rw [hf, zero_mul, zero_mul]

theorem fockF_ten {ι : Type} [Fintype ι] {n : ℕ} (f g : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.REAL.fockF (ten f) (ten g) = ∏ τ, Formalism.REAL.fockF (f τ) (g τ) := by
  rw [fockF_eq_fockL]
  show Formalism.L2.DIV.fockL (∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (g τ)) (∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (f τ)) = _
  rw [Formalism.L2.DIV.fk_fock_prod]
  exact Finset.prod_congr rfl fun τ _ => (fockF_eq_fockL _ _).symm

theorem fockF_extremal_ne {n : ℕ} (l : DomWeight n) : Formalism.REAL.fockF (extremal ℂ n l) (extremal ℂ n l) ≠ 0 := by
  intro h0
  have h1 : normFock l (extremal ℂ n l) (extremal ℂ n l) = 1 := bridge_normFock_extremal_holds n l
  rw [normFock, h0, div_zero] at h1
  exact zero_ne_one h1

theorem nfAll_ten : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), (∀ f g : ι → MvPolynomial (Fin n × Fin n) ℂ, nfAll lam (ten f) (ten g) = ∏ τ, normFock (lam τ) (f τ) (g τ)) ∧ (∀ p : MvPolynomial (ι × Fin n × Fin n) ℂ, nfAll lam p p = 0 → p = 0) ∧ ∀ (G M : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) (y : Frames G), fnOf G s M (ten f) y = ∏ τ, ((M τ * y.1 τ).det ^ s τ * MvPolynomial.eval (fun v : Fin n × Fin n => (M τ * y.1 τ) v.1 v.2) (f τ)) := by
  intro ι _ n lam
  have hden : ∏ τ, Formalism.REAL.fockF (extremal ℂ n (lam τ)) (extremal ℂ n (lam τ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun τ _ => fockF_extremal_ne (lam τ)
  refine ⟨fun f g => ?_, fun p hp => ?_, fun G M s f y => ?_⟩
  · rw [nfAll, fockF_ten]
    simp only [normFock]
    rw [Finset.prod_div_distrib]
  · rw [nfAll, div_eq_zero_iff] at hp
    rcases hp with hp | hp
    · by_contra hne
      exact (@LT.lt.ne' ℂ Complex.partialOrder.toPreorder _ _ (Formalism.L2.DIV.ps_fockF_pos p hne)) hp
    · exact absurd hp hden
  · show (∏ τ, (M τ * y.1 τ).det ^ s τ) *
        MvPolynomial.eval _ (∏ τ, MvPolynomial.rename (Prod.mk τ) (f τ)) = _
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [MvPolynomial.eval_rename]
    rfl

end GlobalTheory.FockTen
