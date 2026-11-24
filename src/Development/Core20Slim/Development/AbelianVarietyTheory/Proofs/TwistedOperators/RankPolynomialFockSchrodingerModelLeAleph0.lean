module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExistsStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.SetTheory.Cardinal.Defs
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory.FockCount

open NumberField

theorem incM_map_piInf' {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n m : Type}
    (J : Matrix n m E) {w : InfinitePlace F} (τ : GlobalTheory.AdelicU.EmbOver E w) :
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ) = J.map τ.1 := by
  ext i j
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf, GlobalTheory.AdelicU.compInf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR,
    GlobalTheory.AdelicU.infEmb_tmul]

theorem rank_tens_le (F : Type) [Field F] [NumberField F] (P Q R S : ℕ) :
    Module.rank ℂ (GlobalTheory.RealLift.Tens F P Q R S) ≤ Cardinal.aleph0 := by
  classical
  let b := _root_.Basis.piTensorProduct (R := ℂ)
    (fun _ : InfinitePlace F => MvPolynomial.basisMonomials (Formalism.BasicNotions.TH.Ix P Q × Formalism.BasicNotions.TH.Ix R S) ℂ)
  rw [← b.mk_eq_rank'']
  exact Cardinal.mk_le_aleph0

theorem rank_pol_le_aleph0 : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d r s r' s' : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    Module.rank ℂ (M.Pol B.ψ B.emb) ≤ Cardinal.aleph0 := by
  intro F E _ _ _ _ _ σ B n d r s r' s' X W M hB hX hW _hM
  classical
  have hcm := hB.cm
  have hstd := hB.std
  have hFr : ∀ w, ∃ A : Matrix (Fin n) (Formalism.BasicNotions.TH.Ix r s) ℂ,
      GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) A ∧ X.θ w * A = A * Formalism.BasicNotions.TH.Jm r s := by
    intro w
    rw [incM_map_piInf', one_smul]
    exact GlobalTheory.T.cartanEigen_orthonormalFrame_exists n r s _ _ (hX.sig w) (hX.cartan w)
  have hFrW : ∀ w, ∃ C : Matrix (Fin d) (Formalism.BasicNotions.TH.Ix r' s') ℂ,
      GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) C ∧
        W.θ w * C = C * Formalism.BasicNotions.TH.Jm r' s' := by
    intro w
    rw [incM_map_piInf']
    exact GlobalTheory.T.cartanEigen_orthonormalFrame_exists d r' s' _ _ (hW.sig w) (hW.cartan w)
  choose A hA hAθ using hFr
  choose C hC hCθ using hFrW
  have hFramed : GlobalTheory.RealLift.Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C :=
    ⟨one_mul _, hA, hC⟩
  have hder := GlobalTheory.T.archHeisenbergDerivatives_exist
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder F E σ (Fin n) (Fin d) (Fin n × Fin d) r s r' s' B.ψ B.emb (incM F X.J)
    (incM F W.J) M.co 1 Complex.I A C hcm hstd hFramed
  have hrange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hder (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder) F E σ n d r s r' s' X W M B.ψ B.emb A C Φ
    hcm hstd hFramed hAθ hCθ hΦ
  rw [← hrange]
  exact (rank_range_le Φ).trans (rank_tens_le F r s r' s')

end GlobalTheory.FockCount
