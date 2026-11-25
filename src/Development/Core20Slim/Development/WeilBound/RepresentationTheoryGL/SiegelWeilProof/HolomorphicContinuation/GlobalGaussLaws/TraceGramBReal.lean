module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DBoundB
public import Batteries.Logic
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Init.ByCases
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilAH

variable {D : D7} {n : ℕ}

theorem cLoc_pos {l : D.what₂.Tau → ℝ} {τ : D.what₂.Tau} (h : l τ ≠ 0) : 0 < cLoc l τ := by
  unfold cLoc; have := abs_pos.2 h; positivity

theorem abs_tLoc (l : D.what₂.Tau → ℝ) (τ : D.what₂.Tau) : |tLoc l τ| = cLoc l τ := by
  unfold tLoc cLoc; rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

theorem trace_gramB_real {m : ℕ} (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    (gramB ε b u).trace = ((∑ a ∈ Finset.univ.filter (fun a => ε a = b), ∑ j, ‖u a j‖ ^ 2 : ℝ) : ℂ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramB, evX, Qb, map_sum, map_mul, MvPolynomial.eval_X, if_true, Bool.false_eq_true, if_false,
    Matrix.trace, Matrix.diag]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.conj_mul', Complex.star_def]

theorem sum_filter_bool {m : ℕ} (ε : Fin m → Bool) (f : Fin m → ℝ) :
    ∑ a ∈ Finset.univ.filter (fun a => ε a = true), f a + ∑ a ∈ Finset.univ.filter (fun a => ε a = false), f a =
      ∑ a, f a := by
  rw [← Finset.sum_union]
  · congr 1; ext a; cases ε a <;> simp
  · rw [Finset.disjoint_filter]; intro a _ h; simp [h]

theorem gC_gauss {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (hc : 0 < c) (δ : ℝ) (u : Fin m → Fin n → ℂ) :
    gC ε t c ((Complex.I * (δ / c : ℝ)) • 1) ((-(Complex.I * (δ / c : ℝ))) • 1) u =
      Complex.exp (-((δ * ∑ a, ∑ j, ‖u a j‖ ^ 2 : ℝ) : ℂ)) := by
  unfold gC
  congr 1
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul, trace_gramB_real]
  have h := sum_filter_bool (epsT t ε) (fun a => ∑ j, ‖u a j‖ ^ 2)
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [← h]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem fP_one {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (hc : 0 < c) :
    fP c (1 : PX m n) = gZf ε t c (Complex.I • 1) := by
  funext u
  have e1 : gZf ε t c (Complex.I • 1) u = gC ε t c ((Complex.I * (c / c : ℝ)) • 1) ((-(Complex.I * (c / c : ℝ))) • 1) u := by
    unfold gZf gC
    rw [div_self hc.ne', Complex.ofReal_one, mul_one, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Complex.star_def, Complex.conj_I]
  rw [e1, gC_gauss ε t c hc c u]
  simp [fP, evX, gs]

end PositivityTheory.Rg.Sw.Glob.DilAH
