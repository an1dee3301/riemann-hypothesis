module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLatticesFormSelfDualTriples
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PIopIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.SkewTheta

theorem semiChar_of_nice {D : D7} {T : Tor D} {N N' : ℕ} {A : AddSubgroup (VC D N N')}
    (h : GlobalTheory.InertSign.Nice D T A) : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.SemiChar T A := by
  intro x hx y hy
  have hW := GlobalTheory.InertSign.Wd_Wd D T x y (fun _ => (1 : ℂ))
  rw [h.2.1 x hx y hy, one_smul, h.1 _ (A.add_mem hx hy), h.1 y hy] at hW
  have hz := congrFun hW 0
  rw [h.1 x hx] at hz
  simp only at hz
  rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.U_smul, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.U_U] at hz
  have hU : U D T (x + y) (fun _ => (1 : ℂ)) 0 ≠ 0 := by
    simp only [U, one_mul]
    exact Complex.exp_ne_zero _
  refine mul_right_cancel₀ hU ?_
  rw [← hz]; ring

theorem iop_mem_thSp : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (𝔪 : Ideal (𝓞 D.host.E)), SD D (skewLat D 𝔪 d) → Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 ∈ ThSp D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) := by
  intro D δ hc a d e0 he0 𝔪 hsd
  have hK : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) :=
    Or.inr ⟨_, _, GlobalTheory.FinWeil.RatTransl.sd_std D a, hsd, rfl⟩
  have hN := (GlobalTheory.ThetaTriple.klat_triples D ⊤ δ hc a d).1 _ hK
  exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Iop_mem_ThSp (tor0 D ⊤ δ) (semiChar_of_nice hN) he0

end GlobalTheory.SkewTheta
