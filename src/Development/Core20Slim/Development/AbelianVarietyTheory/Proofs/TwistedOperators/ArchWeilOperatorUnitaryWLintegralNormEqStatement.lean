module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchWeilOperatorUnitaryWLintegralNormEq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchActOne
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archWeilOperator_unitaryW_lintegral_norm_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) →
    ∀ h ∈ UAt σ W (evI F), ∀ (N : ℕ) (C : (Fin n × Fin d → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin N))
      (f : SInf F (Fin n × Fin d)),
      ∫⁻ x, ‖archOp om h f (C.symm x)‖ₑ ^ 2 = ∫⁻ x, ‖f (C.symm x)‖ₑ ^ 2 := by
  first | exact @GlobalTheory.ArchimedeanLineL2.archOp_lintegral_eq | exact GlobalTheory.ArchimedeanLineL2.archOp_lintegral_eq | (intros; apply GlobalTheory.ArchimedeanLineL2.archOp_lintegral_eq <;> assumption)
