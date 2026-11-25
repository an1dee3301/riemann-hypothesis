module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GaussPart
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem cnt_add (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun a => ε a = true)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have h2 : (Finset.univ.filter fun a => ε a = false) = Finset.univ.filter fun a => ¬ ε a = true := by
    ext a; simp
  rw [h2]
  exact h

theorem bS_herm (X : Fin n → ℝ) (h : ℝ) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : (bS X h b).IsHermitian := by
  have hD : (diagonal (fun j => (Real.exp (-(h * X j)) : ℂ)))ᴴ = diagonal (fun j => (Real.exp (-(h * X j)) : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext j
    exact Complex.conj_ofReal _
  unfold bS Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hD, hb.eq, Matrix.mul_assoc]

theorem derivative_vacuum_of_parts (hG : GaussPart) (hH : GroupPart) : DerivativeVacuumDilations := by
  intro m n ε c t p q e sL ρ hL X a hA y r
  obtain ⟨hadd, ha0, hup, hcont, hupmul, hdec, hconj, hcellinv, hdense, hF0⟩ := hH n X a hA
  obtain ⟨C, hC0, hcell⟩ := hL.cell
  have hpq : p + q = m := by
    rcases hL.sign with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · exact cnt_add ε
    · rw [add_comm]; exact cnt_add ε
  have hneg : ∀ h : ℝ, a (-h) * a h = 1 := by
    intro h; rw [← hadd, neg_add_cancel, ha0]

  have L1 : ∀ (Q : PX m n) (y : GR n), (mR y).toBlocks₂₁.det ≠ 0 →
      HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) y) 0 := by
    intro Q y hy
    obtain ⟨y₁, g, b, hy₁, hb, hg, rfl⟩ := hdec y hy
    have hfun : (fun h => sL Q (y₁ * g * a h)) = fun h => (F0 p q e y₁ * C) *
        (Complex.exp (-((h * ((m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) * secN ε c t Q (bS X h b)) := by
      funext h
      have e1 : y₁ * g * a h = (y₁ * a (-h)) * (a h * g * a h) := by
        calc y₁ * g * a h = y₁ * (a (-h) * a h) * g * a h := by rw [hneg, mul_one]
          _ = _ := by group
      have e2 : F0 p q e (y₁ * a (-h)) = F0 p q e y₁ * F0 p q e (a (-h)) := by
        rw [← hL.vac, hL.law 1 _ _ hy₁, hL.vac]
      have e3 : F0 p q e (a (-h)) = Complex.exp (-((h * ((m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) := by
        rw [hF0, hpq]
      rw [e1, hL.law Q _ _ (hupmul y₁ hy₁ (-h)), e2, e3, hcell Q _ _ (bS_herm X h hb) (hconj g b hg h)]
      ring
    rw [hfun]
    have hv : sL (dil c X Q) (y₁ * g) = (F0 p q e y₁ * C) * secN ε c t (dil c X Q) b := by
      rw [hL.law _ _ _ hy₁, hcell _ _ _ hb hg]; ring
    rw [hv]
    exact (hG m n ε c t hL.cpos X b hb Q).const_mul _

  have L2 : ∀ (Q : PX m n) (y : GR n), (mR y).toBlocks₂₁.det ≠ 0 → ∀ s,
      HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) (y * a s)) s := by
    intro Q y hy s
    have h0 := L1 Q (y * a s) (hcellinv y hy s)
    have h0' : HasDerivAt (fun h => sL Q (y * a s * a h)) (sL (dil c X Q) (y * a s)) (s - s) := by
      rw [sub_self]; exact h0
    have h1 := HasDerivAt.comp_sub_const s s h0'
    have hf : (fun x => sL Q (y * a x)) = fun x => sL Q (y * a s * a (x - s)) := by
      funext x
      rw [mul_assoc, ← hadd, add_sub_cancel]
    rw [hf]
    exact h1
  have hjc : ∀ (Q : PX m n), Continuous (fun z : GR n × ℝ => sL Q (z.1 * a z.2)) := fun Q =>
    (hL.cont Q).comp (continuous_fst.mul (hcont.comp continuous_snd))

  have L3 : ∀ (Q : PX m n) (s : ℝ) (y : GR n),
      sL Q (y * a s) - sL Q y = ∫ u in (0 : ℝ)..s, sL (dil c X Q) (y * a u) := by
    intro Q s
    have hc1 : Continuous fun y : GR n => sL Q (y * a s) - sL Q y :=
      ((hL.cont Q).comp (continuous_id.mul continuous_const)).sub (hL.cont Q)
    have hc2 : Continuous fun y : GR n => ∫ u in (0 : ℝ)..s, sL (dil c X Q) (y * a u) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (hjc (dil c X Q)) continuous_const
    intro y0
    refine congrFun (Continuous.ext_on hdense hc1 hc2 ?_) y0
    intro y hy
    show sL Q (y * a s) - sL Q y = ∫ u in (0 : ℝ)..s, sL (dil c X Q) (y * a u)
    have hd : ∀ x ∈ Set.uIcc (0 : ℝ) s, HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) (y * a x)) x :=
      fun x _ => L2 Q y hy x
    have hint : IntervalIntegrable (fun u => sL (dil c X Q) (y * a u)) volume 0 s :=
      ((hL.cont (dil c X Q)).comp (continuous_const.mul hcont)).intervalIntegrable 0 s
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint, ha0, mul_one]
  have L4 : ∀ (Q : PX m n) (y : GR n) (s : ℝ),
      HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) (y * a s)) s := by
    intro Q y s
    have hgc : Continuous fun u => sL (dil c X Q) (y * a u) := (hL.cont _).comp (continuous_const.mul hcont)
    have h1 := (hgc.integral_hasStrictDerivAt 0 s).hasDerivAt
    have h2 := h1.const_add (sL Q y)
    have hf : (fun h => sL Q (y * a h)) = fun x => sL Q y + ∫ u in (0 : ℝ)..x, sL (dil c X Q) (y * a u) := by
      funext x
      rw [← L3 Q x y]; ring
    rw [hf]
    exact h2
  have L5 : ∀ k : ℕ, iteratedDeriv k (fun s => F0 p q e (y * a s)) = fun s => sL ((dil c X ^ k) 1) (y * a s) := by
    intro k
    induction k with
    | zero => funext s; simp [hL.vac]
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      rw [(L4 _ y s).deriv, pow_succ', Module.End.mul_apply]
  refine ⟨?_, ?_⟩
  · rw [L5 r]
    have := L4 ((dil c X ^ r) 1) y 0
    rw [ha0, mul_one, ← Module.End.mul_apply, ← pow_succ'] at this
    exact this
  · rw [L5 r]
    show sL ((dil c X ^ r) 1) (y * a 0) = _
    rw [ha0, mul_one]

end PositivityTheory.Rg.Sw.AbsSt.DF
