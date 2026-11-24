module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PoissonSummationAdelicTuples
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsArchimedeanExponentsAdeleCharacter
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelesHaarMeasureCovolumeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.PoissonReindex

open GlobalTheory.SWQ

variable {F : Type} [Field F] [NumberField F]

def reidx {κ ι : Type} (e : κ ≃ ι) : (ι → AF F) ≃ₜ+ (κ → AF F) where
  toFun u i := u (e i)
  invFun x j := x (e.symm j)
  left_inv u := by funext j; simp
  right_inv x := by funext i; simp
  map_add' u v := rfl
  continuous_toFun := continuous_pi fun i => continuous_apply _
  continuous_invFun := continuous_pi fun j => continuous_apply _

theorem reidx_apply {κ ι : Type} (e : κ ≃ ι) (u : ι → AF F) (i : κ) : reidx (F := F) e u i = u (e i) := rfl

theorem dot_reidx {κ ι : Type} [Fintype κ] [Fintype ι] (e : κ ≃ ι) (u y : ι → AF F) :
    reidx e u ⬝ᵥ reidx e y = u ⬝ᵥ y := by
  simp only [dotProduct, reidx_apply]
  exact e.sum_comp (fun j => u j * y j)

theorem Bd_half {N : ℕ} (s u : Fin N → AF F) : Bd (AF F) (fun _ : Fin N => (1 / 2 : F)) s u = s ⬝ᵥ u := by
  simp only [Bd, dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (2 : F) * (1 / 2) = 1 by norm_num, map_one, one_mul]

theorem mem_schA_reidx {κ ι : Type} [Fintype κ] [Fintype ι] (e : κ ≃ ι) {Φ : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ schA F κ) : (fun u => Φ (reidx e u)) ∈ schA F ι := by
  have h := GlobalTheory.RestrSchA.mem_schA_comp_extend F e.symm e.symm.injective Φ hΦ
  convert h using 2 with u
  congr 1
  funext i
  rw [reidx_apply]
  conv_rhs => rw [← e.symm_apply_apply i]
  exact (e.symm.injective.extend_apply u 0 (e i)).symm

end GlobalTheory.PoissonReindex


