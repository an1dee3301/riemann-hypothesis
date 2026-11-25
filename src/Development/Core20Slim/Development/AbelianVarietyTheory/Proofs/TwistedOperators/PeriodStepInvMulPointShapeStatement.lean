module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodStepInvMulPointShape
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepLin
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv GlobalTheory.StepLeft Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodStep_inv_mul_point_shape : ∀ {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (v : GL (n ⊕ Fin c) k), v ∈ symN k n c → ∀ (κ : GL n k) (x₀ : Matrix n n' k) (e : StepVar n c n' → k), ((v * embX c κ)⁻¹).val * stepPt x₀ e = stepPt ((κ⁻¹).val * x₀) (fun a => (((v * embX c κ)⁻¹).val * stepPt x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) a.1.1 a.1.2) := by
  first | exact @GlobalTheory.StepLeft.inv_mul_stepPt_shape | exact GlobalTheory.StepLeft.inv_mul_stepPt_shape | (intros; apply GlobalTheory.StepLeft.inv_mul_stepPt_shape <;> assumption)
