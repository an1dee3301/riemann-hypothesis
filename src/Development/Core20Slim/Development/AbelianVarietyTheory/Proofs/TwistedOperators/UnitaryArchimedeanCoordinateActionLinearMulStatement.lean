module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionLinearMul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchActOne
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_archimedean_coordinate_action_linear_mul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W),
    (∀ (h : UA σ W.J) (v v' : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M h (v + v') = archAct M h v + archAct M h v') ∧
    (∀ (h : UA σ W.J) (c : ℝ) (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M h (c • v) = c • archAct M h v) ∧
    (∀ (h h' : UA σ W.J) (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M (h * h') v = archAct M h (archAct M h' v)) := by
  intro F E _ _ _ _ _ σ n d X W M
  exact GlobalTheory.ArchLine.archAct_linear_mul M
