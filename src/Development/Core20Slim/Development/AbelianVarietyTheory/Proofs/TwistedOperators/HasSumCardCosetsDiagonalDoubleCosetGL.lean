module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParamTrivialBoundUnitaryGLStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumHeckeEigenvalueGeneratingSeriesGLStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FiniteCosetsInDoset
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementE
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Quot
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Monotone.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FinZeta.TrivCount

theorem trivial_isUnitarisable {G : Type} [Group G] :
    IsUnitarisable (Representation.trivial ℂ G ℂ) := by
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => x * starRingEnd ℂ y)
      (fun _ _ _ => add_mul _ _ _) (fun _ _ _ => by simp [mul_assoc])
      (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp [mul_left_comm]), ?_, ?_, ?_⟩
  · intro v w; simp [mul_comm]
  · intro v hv; simpa [Complex.mul_conj] using hv
  · intro g v w; simp

theorem heckeVec_trivial_dosetInd {G : Type} [Group G] {K : Subgroup G} (hK : IsCommensurated K) (t : G) :
    heckeVec (Representation.trivial ℂ G ℂ) K (dosetInd ℂ K t) 1 =
      ((Nat.card {a : G ⧸ K // a.out ∈ DoubleCoset.doubleCoset t (K : Set G) K} : ℝ) : ℂ) • 1 := by
  classical
  set D := DoubleCoset.doubleCoset t (K : Set G) K
  have hfin : {a : G ⧸ K | a.out ∈ D}.Finite := by
    refine (Formalism.UG.P.finite_support_cosets hK (Formalism.UG.Final.DosetIndMem G K ℂ t).2).subset ?_
    intro a ha
    have h' : a.out ∈ D := ha
    simp only [Set.mem_setOf_eq, dosetInd]
    rw [Set.indicator_of_mem h']
    simp
  have e : (fun c : G ⧸ K => dosetInd ℂ K t c.out • (Representation.trivial ℂ G ℂ) c.out (1 : ℂ)) =
      Set.indicator {a : G ⧸ K | a.out ∈ D} 1 := by
    funext c
    by_cases h : c.out ∈ D <;> simp [dosetInd, D, h, Set.indicator]
  rw [heckeVec, e, ← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hc : Nat.card {a : G ⧸ K // a.out ∈ D} = hfin.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact Nat.card_coe_set_eq {a : G ⧸ K | a.out ∈ D}
  rw [hc]
  simp

theorem hasSum_card_cosets_diag : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E), (∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i) → ∃ B₀ : Multiset ℂˣ, (∀ β ∈ B₀, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℝ, 0 < X → X < δ → HasSum (fun d : {d : Fin r → ℤ // Antitone d} => ((Nat.card {a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) // a.out ∈ DoubleCoset.doubleCoset (T d.1) (KGL w (n := r) : Set (GL (Fin r) (w.adicCompletion E))) (KGL w (n := r))} : ℝ) : ℂ) * (X : ℂ) ^ (∑ i, |d.1 i|).toNat) (eulerFac B₀ ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * eulerFac (B₀.map (·⁻¹)) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X : ℂ) ^ 2)) := by
  intro hP E _ _ w r ϖ hϖ T hT
  have hK : IsCommensurated (KGL w (n := r)) := Formalism.UG.Final.GLintComm E w r
  let ρ := Representation.trivial ℂ (GL (Fin r) (w.adicCompletion E)) ℂ
  have hu : IsUnitarisable ρ := trivial_isUnitarisable
  have hfix : (1 : ℂ) ∈ fixed ρ (KGL w (n := r)) := GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl
  have heig : ∀ h ∈ Hecke ℂ (KGL w (n := r)), ∃ c : ℂ, heckeVec ρ (KGL w (n := r)) h 1 = c • (1 : ℂ) :=
    fun h _ => ⟨heckeVec ρ (KGL w (n := r)) h 1, by rw [smul_eq_mul, mul_one]⟩
  obtain ⟨B, hB, hbd⟩ := GlobalTheory.T.exists_satakeParam_trivialBound_unitaryGL E w r ℂ ρ hu 1 one_ne_zero hfix heig
  have hc : ∀ d, heckeVec ρ (KGL w (n := r)) (dosetInd ℂ (KGL w (n := r)) (T d)) 1 =
      (fun d => ((Nat.card {a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) // a.out ∈
        DoubleCoset.doubleCoset (T d) (KGL w (n := r) : Set (GL (Fin r) (w.adicCompletion E))) (KGL w (n := r))} : ℝ) : ℂ)) d
        • (1 : ℂ) := fun d => heckeVec_trivial_dosetInd hK (T d)
  refine ⟨B, hbd, ?_⟩
  have key := GlobalTheory.T.hasSum_heckeEigenvalue_generatingSeries_GL hP E w r ℂ ρ 1 B hB ϖ hϖ T hT _ hc
  beta_reduce at key
  exact key

end GlobalTheory.FinZeta.TrivCount
