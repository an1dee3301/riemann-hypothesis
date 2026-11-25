module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.Core20Slim.GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrSumOf
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.IntegersLattice
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.TracePairing
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

namespace GlobalTheory.StdCharEq

theorem trace_eq_infiniteTrace (F : Type) [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) =
      GroundTheory.Global.infiniteTrace F x := by
  classical
  rw [← GroundTheory.Global.mixedTrace_homeomorphMixedSpace, GroundTheory.Global.homeomorphMixedSpace_apply,
    GroundTheory.Global.mixedTrace_apply, Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi,
    PI.ProdFormulaE.Tr.trace_pi]
  simp only [Algebra.trace_self_apply, Algebra.trace_complex_apply]

theorem eq_adelicChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ x : AF F, ψ x = (GroundTheory.Global.adelicChar F x : ℂ) := by
  intro F _ _ ψ hψ
  have hadd : ∀ a b : AF F, (GroundTheory.Global.adelicChar F (a + b) : ℂ) =
      (GroundTheory.Global.adelicChar F a : ℂ) * (GroundTheory.Global.adelicChar F b : ℂ) := fun a b => by
    rw [← Circle.coe_mul]
    exact congrArg _ ((GroundTheory.Global.adelicChar F).map_add_eq_mul a b)
  have hinf : ∀ x : Ainf F, ψ (pairA F x 0) = (GroundTheory.Global.adelicChar F (pairA F x 0) : ℂ) := fun x => by
    have h : GroundTheory.Global.adelicChar F (pairA F x 0) = 𝐞 (-GroundTheory.Global.infiniteTrace F x) :=
      GroundTheory.Global.adelicChar_infinite x
    rw [GlobalTheory.StdCharFromIsStd.psi_pairA hψ, trace_eq_infiniteTrace, h, Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  have hp : Continuous fun y : Af F => pairA F 0 y := continuous_const.prodMk continuous_id
  have hc : Continuous fun a : AF F => (GroundTheory.Global.adelicChar F a : ℂ) :=
    continuous_subtype_val.comp GroundTheory.Global.continuous_adelicChar
  have hcl : IsClosed {y : Af F | ψ (pairA F 0 y) = (GroundTheory.Global.adelicChar F (pairA F 0 y) : ℂ)} :=
    isClosed_eq (hψ.1.comp hp) (hc.comp hp)
  have hrange : Set.range (algebraMap F (Af F)) ⊆
      {y : Af F | ψ (pairA F 0 y) = (GroundTheory.Global.adelicChar F (pairA F 0 y) : ℂ)} := by
    rintro _ ⟨a, rfl⟩
    have h1 := hψ.2.1 a
    have h2 : (GroundTheory.Global.adelicChar F (algebraMap F (AF F) a) : ℂ) = 1 := by
      have h := GroundTheory.Global.adelicChar_algebraMap (K := F) a
      exact (congrArg (fun z : Circle => (z : ℂ)) h).trans Circle.coe_one
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, AddChar.map_add_eq_mul, hinf] at h1
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, hadd] at h2
    exact mul_left_cancel₀ (Circle.coe_ne_zero _) (h1.trans h2.symm)
  have hall := hcl.closure_subset_iff.2 hrange
  rw [GlobalTheory.AdeleCharTwist.denseRange_fin.closure_range] at hall
  intro x
  rw [GlobalTheory.StdCharFromIsStd.pairA_split x, AddChar.map_add_eq_mul, hadd, hinf]
  exact congrArg _ (hall (Set.mem_univ x.2))

end GlobalTheory.StdCharEq
