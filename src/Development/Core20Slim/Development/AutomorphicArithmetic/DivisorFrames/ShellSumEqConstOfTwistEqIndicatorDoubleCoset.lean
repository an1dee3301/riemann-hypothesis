module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumVolShellInterTranslate
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.shellSum_eq_const_of_twist_eq_indicator_double_coset :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ →
        ∀ (a : ℕ) (ν : kˣ →* ℂˣ) (z C : ℂ) (φ : Matrix (Fin a) (Fin a) k → ℂ) (g₀ g₁ : GL (Fin a) k),
        (∀ g : GL (Fin a) k, φ g.1 * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) z =
          {g : GL (Fin a) k | g₀ * g * g₁ ∈ GlobalTheory.SplitWeil.KO k (Fin a)}.indicator (fun _ => C) g) →
        GlobalTheory.SplitFlip.shellSum (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ ν z φ = C := by
  intro k _ _ _ _ _ _ ϖ hϖ a ν z C φ g₀ g₁ hφ
  letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
  haveI : BorelSpace (GL (Fin a) k) := GlobalTheory.SplitFlip.borel_GL
  have hSm : MeasurableSet {g : GL (Fin a) k | g₀ * g * g₁ ∈ GlobalTheory.SplitWeil.KO k (Fin a)} :=
    (GlobalTheory.PureMatch.ShellVolume.isOpen_translate g₀ g₁).measurableSet
  have hvol := GlobalTheory.PureMatch.ShellVolume.finsum_vol_shell_inter_translate k a ϖ g₀ g₁ hϖ
  have hshell : ∀ m : {m : Fin a → ℤ // Antitone m},
      GlobalTheory.SplitFlip.shell (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ ν z φ m.1 =
      (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))).real (GlobalTheory.SplitFlip.shellSet ϖ m.1 ∩
        {g : GL (Fin a) k | g₀ * g * g₁ ∈ GlobalTheory.SplitWeil.KO k (Fin a)}) • C := by
    intro m
    rw [GlobalTheory.SplitFlip.shell]
    simp_rw [hφ]
    have e1 := MeasureTheory.setIntegral_indicator (μ := GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a)))
      (s := GlobalTheory.SplitFlip.shellSet ϖ m.1) (f := fun _ => C) hSm
    rw [e1, MeasureTheory.setIntegral_const]
  rw [GlobalTheory.SplitFlip.shellSum]
  simp_rw [hshell]
  rw [← finsum_smul, hvol, one_smul]
