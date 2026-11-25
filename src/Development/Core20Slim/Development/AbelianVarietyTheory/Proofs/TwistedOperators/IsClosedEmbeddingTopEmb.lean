module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatSweepSmoothlyInducedStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGLMulRightColumnsEqZeroOfRankStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftColumnsMulVecInjectiveOfRankEqCardStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankFiltrationExists
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences Matrix Topology
open scoped TensorProduct

namespace GlobalTheory.RankStrataProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lower

variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]


open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype b] [DecidableEq a]
  [DecidableEq b] [DecidableEq c] [DecidableEq d] in
theorem _root_.GlobalTheory.RankStrataProof.mul_apply_of_cols {n : Type} (e : c ⊕ d ≃ a) {x : Matrix b a k} (hx : ∀ i j, x i (e (.inr j)) = 0)
    (g : Matrix a n k) (i : b) (l : n) : (x * g) i l = ∑ m, x i (e (.inl m)) * g (e (.inl m)) l := by
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_sum_type]
  simp [hx]

def rAct (s : Set ℕ) (x : RankIn k a b s) (g : GL a k) : RankIn k a b s :=
  ⟨act x.1 (g, 1), by rw [rank_act]; exact x.2⟩

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.rAct_val (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g : GL a k) : (_root_.GlobalTheory.RankStrataProof.rAct s x g).1 = x.1 * g.val := by
  unfold _root_.GlobalTheory.RankStrataProof.rAct _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.act
  simp

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.rAct_one (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) : _root_.GlobalTheory.RankStrataProof.rAct s x 1 = x := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.rAct_val]
  simp

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.rAct_mul (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g h : GL a k) :
    _root_.GlobalTheory.RankStrataProof.rAct s x (g * h) = _root_.GlobalTheory.RankStrataProof.rAct s (_root_.GlobalTheory.RankStrataProof.rAct s x g) h := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.rAct_val, _root_.GlobalTheory.RankStrataProof.rAct_val, _root_.GlobalTheory.RankStrataProof.rAct_val, Units.val_mul, Matrix.mul_assoc]




open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
theorem _root_.GlobalTheory.RankStrataProof.isSmoothChar_omChar {μ : kˣ →* ℂˣ} (hμ : _root_.GlobalTheory.SmGL.IsSmoothChar μ) : _root_.GlobalTheory.SmGL.IsSmoothChar (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.omChar a b μ) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.omChar
  apply _root_.GlobalTheory.SmGL.IsSmoothChar.mul
  · refine _root_.GlobalTheory.SmGL.IsSmoothChar.comp ?_ _ continuous_fst
    apply _root_.GlobalTheory.SmGL.IsSmoothChar.detChar
    exact _root_.GlobalTheory.SmGL.IsSmoothChar.mul
      (_root_.GlobalTheory.SmGL.IsSmoothChar.inv hμ)
      (_root_.GlobalTheory.SmGL.isSmoothChar_of_isUnram (_root_.GlobalTheory.SmGL.isUnram_absPow k _))
  · refine _root_.GlobalTheory.SmGL.IsSmoothChar.comp ?_ _ continuous_snd
    apply _root_.GlobalTheory.SmGL.IsSmoothChar.detChar
    exact _root_.GlobalTheory.SmGL.IsSmoothChar.mul hμ
      (_root_.GlobalTheory.SmGL.isSmoothChar_of_isUnram (_root_.GlobalTheory.SmGL.isUnram_absPow k _))

end Lower

section Open

variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]






def lAct (s : Set ℕ) (x : RankIn k a b s) (h : GL b k) : RankIn k a b s :=
  ⟨act x.1 (1, h), by rw [rank_act]; exact x.2⟩

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.lAct_val (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g : GL b k) : (_root_.GlobalTheory.RankStrataProof.lAct s x g).1 = (g⁻¹).val * x.1 := by
  unfold _root_.GlobalTheory.RankStrataProof.lAct _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.act
  simp

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.lAct_one (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) : _root_.GlobalTheory.RankStrataProof.lAct s x 1 = x := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.lAct_val]
  simp

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.lAct_mul (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g h : GL b k) :
    _root_.GlobalTheory.RankStrataProof.lAct s x (g * h) = _root_.GlobalTheory.RankStrataProof.lAct s (_root_.GlobalTheory.RankStrataProof.lAct s x g) h := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.lAct_val, _root_.GlobalTheory.RankStrataProof.lAct_val, _root_.GlobalTheory.RankStrataProof.lAct_val, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] in
theorem _root_.GlobalTheory.RankStrataProof.continuous_lAct (s : Set ℕ) : Continuous fun p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s × GL b k => _root_.GlobalTheory.RankStrataProof.lAct s p.1 p.2 := by
  have h : Continuous fun p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s × GL b k => ((p.2⁻¹ : GL b k) : Matrix b b k) * p.1.1 :=
    (Units.continuous_val.comp (continuous_inv.comp continuous_snd)).matrix_mul
      (continuous_subtype_val.comp continuous_fst)
  refine Continuous.subtype_mk (h.congr fun p => (_root_.GlobalTheory.RankStrataProof.lAct_val s p.1 p.2).symm) _

end Open

end GlobalTheory.RankStrataProof
