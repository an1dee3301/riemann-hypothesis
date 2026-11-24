module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocKvacA
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPolynomialSchwartzKilledByLongAnnihilation
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoC
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoD
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoF
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem const_of_annS {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian) (l : D.what₂.Tau → ℝ)
    (Q : PX V.rank n) (h : ∀ X, annS V l s θ τ X (tens θ τ fr (fP (cLoc l τ) Q) (psi0 θ V n l s τ)) = 0) :
    Q = C (evX Q 0) := by
  have hk : ∀ u W : Matrix (Fin V.rank) (Fin n) ℂ, ∑ k, ptX W k * eval (ptX u) (pderiv k Q) = 0 := by
    intro u W
    have e := congrFun (h (fr * W)) (xL θ τ (fr * u))
    rw [annS_tens hθ hfr hM l] at e
    have hinv : ∀ v : Matrix (Fin V.rank) (Fin n) ℂ, fr⁻¹ * (fr * v) = v := fun v => by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr.1, Matrix.one_mul]
    have hc : compAt θ τ (xL θ τ (fr * u)) = fr * u := by
      have := congrFun (compAt_xL hθ τ (fr * u)) τ
      simpa [dirAt_self] using this
    have hp : psi0 θ V n l s τ (xL θ τ (fr * u)) = 1 := by
      unfold psi0
      rw [compAt_xL hθ, gAway_dirAt, finPart_xL hθ]
      simp only [one_mul]
      exact gaussian_at_zero_eq_one D V.rank n
    rw [hc, hinv, hinv, hp, mul_one] at e
    exact (mul_eq_zero.1 e).resolve_right (gs_ne_zero _ _)
  have hconst : ∀ u : Matrix (Fin V.rank) (Fin n) ℂ, evX Q u = evX Q 0 := by
    intro u
    let F : ℝ → ℂ := fun t => eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • ptX u) Q
    have hF : ∀ t, HasDerivAt F 0 t := by
      intro t
      have hd := GlobalTheory.FockAnnKill.hasDerivAt_eval_line Q (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ)) (ptX u) t
      refine hd.congr_deriv ?_
      have e2 : ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • ptX u = ptX ((0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • u) :=
        (ptX_add_smul _ _ t).symm
      rw [e2]
      exact hk _ u
    have hdiff : Differentiable ℝ F := fun t => (hF t).differentiableAt
    have hc := is_const_of_deriv_eq_zero hdiff (fun t => (hF t).deriv) 1 0
    have e1 : F 1 = evX Q u := by
      show eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ((1 : ℝ) : ℂ) • ptX u) Q = eval (ptX u) Q
      rw [Complex.ofReal_one, one_smul]
      have e3 : ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ptX u = ptX u := by
        funext k
        obtain ⟨a, i, b⟩ := k
        cases b <;> simp [ptX]
      rw [e3]
    have e0 : F 0 = evX Q 0 := by
      show eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ((0 : ℝ) : ℂ) • ptX u) Q = eval (ptX 0) Q
      rw [Complex.ofReal_zero, zero_smul, add_zero]
    rw [← e1, ← e0, hc]
  apply sub_eq_zero.1
  apply evX_eq_zero
  intro u
  show eval _ (Q - C (evX Q 0)) = 0
  rw [map_sub, eval_C]
  exact sub_eq_zero.2 (hconst u)

end PositivityTheory.Rg.Sw.Glob.RhoH
