module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumCompBoundedFibresLeStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndexStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamIsLatticeStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeQuotientTorsionNonzeroStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPowStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeOfDualPairingStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorIndexBoundStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorNormQuadraticExtensionStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPrincipalElementNormBoundStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeNormCmAbsNormStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmConjugationPropertiesStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionOrthogonalityIntegralSolutionStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockMatrixMultiplicativeStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockQuotientInjectionStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionNormZetaBoundStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Quot
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU

variable {E : Type} [Field E] [NumberField E] {m : ℕ}

theorem fibre_bound (c : Matrix (Fin m) (Fin m) E) (b : (Fin m → E) ⧸ lam c) :
    Finite {U : (Fin m → E) ⧸ intVec E m //
        (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b} ∧
      Nat.card {U : (Fin m → E) ⧸ intVec E m //
        (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b} ≤ delta c := by
  obtain ⟨hne, hidx⟩ := GlobalTheory.T.delta_eq_lattice_index E m c
  set H := (intVec E m).toAddSubgroup with hH
  set Kg := (lam c).toAddSubgroup with hK
  have hidx' : delta c = (H.addSubgroupOf Kg).index := hidx
  have hcard : Nat.card (Kg ⧸ H.addSubgroupOf Kg) = delta c := by
    rw [hidx']; rfl
  haveI : Finite (Kg ⧸ H.addSubgroupOf Kg) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hne)
  have hw : (Submodule.Quotient.mk (Quotient.out b) : (Fin m → E) ⧸ lam c) = b :=
    Quotient.out_eq' b
  have hmem : ∀ a : {U : (Fin m → E) ⧸ intVec E m //
      (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b},
      Quotient.out a.1 - Quotient.out b ∈ Kg := by
    intro a
    have : (Submodule.Quotient.mk (Quotient.out a.1) : (Fin m → E) ⧸ lam c) =
        Submodule.Quotient.mk (Quotient.out b) := a.2.trans hw.symm
    exact (Submodule.Quotient.eq _).1 this
  let φ : {U : (Fin m → E) ⧸ intVec E m //
      (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b} →
      Kg ⧸ H.addSubgroupOf Kg := fun a => QuotientAddGroup.mk ⟨_, hmem a⟩
  have hφ : Function.Injective φ := by
    intro a a' h
    have h1 := QuotientAddGroup.eq.1 h
    have h2 : -(Quotient.out a.1 - Quotient.out b) + (Quotient.out a'.1 - Quotient.out b) ∈ H :=
      AddSubgroup.mem_addSubgroupOf.1 h1
    have h3 : Quotient.out a.1 - Quotient.out a'.1 ∈ intVec E m := by
      have h4 := neg_mem h2
      have h5 : -(-(Quotient.out a.1 - Quotient.out b) + (Quotient.out a'.1 - Quotient.out b)) =
          Quotient.out a.1 - Quotient.out a'.1 := by abel
      rw [h5] at h4
      exact h4
    apply Subtype.ext
    have h6 : (Submodule.Quotient.mk (Quotient.out a.1) : (Fin m → E) ⧸ intVec E m) =
        Submodule.Quotient.mk (Quotient.out a'.1) := (Submodule.Quotient.eq _).2 h3
    have e1 : (Submodule.Quotient.mk (Quotient.out a.1) : (Fin m → E) ⧸ intVec E m) = a.1 :=
      Quotient.out_eq' _
    have e2 : (Submodule.Quotient.mk (Quotient.out a'.1) : (Fin m → E) ⧸ intVec E m) = a'.1 :=
      Quotient.out_eq' _
    rw [← e1, ← e2, h6]
  refine ⟨Finite.of_injective φ hφ, ?_⟩
  rw [← hcard]
  exact Nat.card_le_card_of_injective φ hφ

theorem sum_tor : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (c : Matrix (Fin m) (Fin m) E) (r : ℝ), 1 < r → Summable (fun U : (Fin m → E) ⧸ intVec E m => (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r))) ∧ ∑' U : (Fin m → E) ⧸ intVec E m, (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) ≤ delta c * zetaR E r := by
  intro E _ _ m c r hr
  obtain ⟨hs, hle⟩ := GlobalTheory.T.torsion_norm_zeta_bound E m (lam c) (GlobalTheory.T.lam_is_lattice E m c) r hr
  have hg : ∀ x : (Fin m → E) ⧸ lam c,
      0 ≤ (Ideal.absNorm (Ideal.torsionOf (𝓞 E) ((Fin m → E) ⧸ lam c) x) : ℝ) ^
        (-((m : ℝ) + r)) := fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  obtain ⟨h1, h2⟩ := GlobalTheory.T.tsum_comp_bounded_fibres_le ((Fin m → E) ⧸ intVec E m) ((Fin m → E) ⧸ lam c)
    (fun U => Submodule.Quotient.mk (Quotient.out U)) (delta c) (fibre_bound c)
    (fun x => (Ideal.absNorm (Ideal.torsionOf (𝓞 E) ((Fin m → E) ⧸ lam c) x) : ℝ) ^
      (-((m : ℝ) + r))) hg hs
  refine ⟨h1, h2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU
