module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Batteries.Logic
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.ConjugateSelfDual.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ModuLocal

theorem infComp_eq_one {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} {u : (AF F)ˣ}
    (hu : At (evFin F v) ((u : AF F) - 1)) (w : NumberField.InfinitePlace F) : (u : AF F).1 w = 1 := by
  have h := hu (pairA F 1 0) (by change evalV F v 0 = 0; exact map_zero _)
  have h' : (1 : Ainf F) * ((u : AF F).1 - 1) = 0 := congrArg Prod.fst h
  rw [one_mul, sub_eq_zero] at h'
  rw [h']
  rfl

theorem finComp_eq_one {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} {u : (AF F)ˣ}
    (hu : At (evFin F v) ((u : AF F) - 1)) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    (u : AF F).2 w = 1 := by
  have h := hu (pairA F 0 (GlobalTheory.AdelicU.singleFin w 1))
    (by change evalV F v (GlobalTheory.AdelicU.singleFin w 1) = 0; exact GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hw) 1)
  have h2 : GlobalTheory.AdelicU.singleFin w 1 * ((u : AF F).2 - 1) = 0 := congrArg Prod.snd h
  have h' := congrArg (evalV F w) h2
  rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul, map_sub, map_zero, sub_eq_zero] at h'
  rw [← (map_one (evalV F w) : evalV F w 1 = 1)]
  exact h'

end GlobalTheory.ModuLocal

theorem GlobalTheory.ModuLocal.distribHaarChar_eq_nabs_of_at : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (u : (AF F)ˣ), At (evFin F v) ((u : AF F) - 1) →
    ((MeasureTheory.distribHaarChar (AF F) u : NNReal) : ℝ) = GlobalTheory.SplitWeil.nabs (Fv F v) (Units.map (evFin F v : AF F →* Fv F v) u) := by
  intro F _ _ v u hu
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing F u, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have hinf : (∏ w : NumberField.InfinitePlace F, ‖(u : AF F).1 w‖ ^ w.mult) = 1 :=
    Finset.prod_eq_one fun w _ => by rw [GlobalTheory.ModuLocal.infComp_eq_one hu w, norm_one, one_pow]
  have hfin : (∏ᶠ w : HeightOneSpectrum (𝓞 F), ‖(u : AF F).2 w‖) = ‖(u : AF F).2 v‖ :=
    finprod_eq_single _ v fun w hw => by rw [GlobalTheory.ModuLocal.finComp_eq_one hu hw, norm_one]
  have hloc := ((GlobalTheory.CompletionNorm.norm_nabs_valuation F v).1 (Units.map (evFin F v : AF F →* Fv F v) u)).1
  refine (congrArg₂ (· * ·) hinf hfin).trans ?_
  rw [one_mul]
  exact hloc
