module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepSmoothAtFinitePlaceStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
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
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.ThK.LocalOps
end GlobalTheory.ThK.LocalOps
namespace GlobalTheory.ThK.LocalOps
theorem theta_kernel_local_operators_act (_hP : FunPr.ThetaLocalInputs) : ActsEx := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v
  have hex : ∀ x : IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J, x.1 ∈ IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) →
      x.2 ∈ IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v) → ∀ φ ∈ WeilM.SB (Fin n × Fin d → Fv F v),
        ∃ φ₁ ∈ WeilM.SB (Fin n × Fin d → Fv F v), IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ₁ :=
    fun x hx1 hx2 φ hφ => acts_exists hP v x hx1 hx2 φ hφ
  refine ⟨fun g hg h hh φ hφ => ?_, fun u hu φ hφ => ?_, T.weilRep_smooth_at_finitePlace B X W M χX χW om r s r' s' hP v hex⟩
  · obtain ⟨φ₁, h1, h2⟩ := hex (g, h) hg hh φ hφ
    exact ⟨φ₁, ⟨h1, h2⟩, fun φ₂ hφ₂ => acts_unique v _ hφ hφ₂.2 h2⟩
  · refine ⟨WeilM.schr (LatVac.psiAt B.ψ v) (LatVac.locCo M.co v u) φ,
      ⟨SchrSB.schr_mem_SB B.ψ hP.base.std.1 v _ φ hφ, VacBridge.rho_acts_locCo M.co B.ψ v u hu φ⟩,
      fun φ₂ hφ₂ => acts_unique v _ hφ hφ₂.2 (VacBridge.rho_acts_locCo M.co B.ψ v u hu φ)⟩
end GlobalTheory.ThK.LocalOps
namespace GlobalTheory.ThK.LocalOps
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
end GlobalTheory.ThK.LocalOps
namespace GlobalTheory.ThK.LocalOps
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
end GlobalTheory.ThK.LocalOps
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_local_operator_action : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.ThK.ActsEx := by
  first | exact @_root_.GlobalTheory.ThK.LocalOps.theta_kernel_local_operators_act | exact _root_.GlobalTheory.ThK.LocalOps.theta_kernel_local_operators_act | (intros; apply _root_.GlobalTheory.ThK.LocalOps.theta_kernel_local_operators_act <;> assumption)
end
