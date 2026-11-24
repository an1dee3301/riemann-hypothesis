module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyAt0Smul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLineStatement
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.FunObj.NormUniq

theorem wd_rat_mem_TT : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}, Crv D cc δ → ∀ {N N' : ℕ} {x : VC D N N'} {M : ℕ}, 0 < M → M • x ∈ La0 D (tor0 D cc δ) N N' → ∀ {F : VC D N N' → ℂ}, F ∈ TT D (tor0 D cc δ) N N' → Wd D (tor0 D cc δ) x F ∈ TT D (tor0 D cc δ) N N' := by
  intro D cc δ hc N N' x M hM hx F hF
  obtain ⟨hd, m, hm, hFm⟩ := hF
  have hg := (GlobalTheory.InducedType.induced_type D).1
  have hint := (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hg cc δ hc N N' (La0 D (tor0 D cc δ) N N')
    (GlobalTheory.NormSum.VacMove.klat _ (GlobalTheory.NormSum.VacMove.moves_one D N) (GlobalTheory.NormSum.VacMove.moves_one D N'))).2.2.1
  refine ⟨GlobalTheory.FinWeil.RatTransl.differentiable_wd x hd, m * M, Nat.mul_pos hm hM, fun y hy => ?_⟩
  have h0 : Wd D (tor0 D cc δ) ((m * M) • y) F = F := by
    rw [mul_smul]; exact hFm _ (AddSubgroup.nsmul_mem _ hy M)
  obtain ⟨k, hk⟩ := hint _ (AddSubgroup.nsmul_mem _ hy m) _ hx
  have e : (m * M) • y = M • (m • y) := by rw [mul_comm, mul_smul]
  funext w
  exact GlobalTheory.FinWeil.RatTransl.wd_wd_of_int h0 k (by rw [e, GlobalTheory.FinWeil.RatTransl.hf_nsmul, hk]) w

end GlobalTheory.FunObj.NormUniq
