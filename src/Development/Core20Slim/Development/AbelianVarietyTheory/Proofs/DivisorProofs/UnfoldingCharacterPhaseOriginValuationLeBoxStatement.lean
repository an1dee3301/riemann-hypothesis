module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingCharacterPhaseOriginValuationLeBox
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorUniformizerExponent
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.OriginBox GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingCharacterPhase_origin_valuation_le_box : ∀ {k : Type} [Field k] [ValuativeRel k] (G : Grid k) (ϖ : kˣ) (a a' : ℤ) (e : Vars G), e ∈ box G ϖ a a' → valuation k (phase (0 : ColArgs G) e) ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) := by
  first | exact @GlobalTheory.OriginBox.phase_origin_le | exact GlobalTheory.OriginBox.phase_origin_le | (intros; apply GlobalTheory.OriginBox.phase_origin_le <;> assumption)
