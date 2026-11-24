module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenKerOfContinuous
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.ChrWSmooth

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_chrW {χ : Chr F E} (hχ : Continuous χ) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    Continuous (chrW χ t) := by
  have hm : Continuous (Units.map (complMap (splitPrime_under t)).toMonoidHom) :=
    Units.continuous_map (GlobalTheory.LFun.SplitChart.continuous_complMap (splitPrime_under t))
  have h1 : Continuous fun x : (Fv F v)ˣ => ((chrW χ t x : ℂˣ) : ℂ) :=
    (continuous_locChar hχ (splitPrime t)).comp hm
  have h2 : Continuous fun x : (Fv F v)ˣ => (((chrW χ t x)⁻¹ : ℂˣ) : ℂ) := by
    have : (fun x : (Fv F v)ˣ => (((chrW χ t x)⁻¹ : ℂˣ) : ℂ)) = fun x => ((chrW χ t x⁻¹ : ℂˣ) : ℂ) := by
      funext x; rw [map_inv]
    rw [this]
    exact h1.comp continuous_inv
  exact Units.continuous_iff.2 ⟨h1, h2⟩

theorem isUnitaryChar_chrW (χ : Chr F E) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    GlobalTheory.SmGL.IsUnitaryChar (chrW χ t) := fun g => by
  show ‖((Circle.toUnits _ : ℂˣ) : ℂ)‖ = 1
  exact Circle.norm_coe _


end GlobalTheory.ChrWSmooth
