module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitaryStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockInUnitarySStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestTypeNotJointShapeSmallerPairsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegWBlattnerLeOfBlattnerConeStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMinimalKTypeSecondMemberStatement
public import Batteries.Classes.RatCast
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
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
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.SmallerSource

theorem discrete_series_gk_admissible_irreducible (X : ProvA) (h5 : admQ5 X) {r s : ℕ} (hrs : 1 ≤ r + s) (lam : Ix r s → ℚ) :
    AdmGK (X.ds r s lam).HK ∧ IrrGK (X.ds r s lam).HK := by
  obtain ⟨hU, -, -⟩ := h5 r s hrs
  set D := X.ds r s lam
  exact (hU D.U ⟨D.nontriv, D.irred⟩).2.2 D.HK D.ι ⟨D.ι_inj, D.ι_range, D.der⟩

theorem cPair_sub {p q i : ℕ} (hp : i ≤ p) (hq : i ≤ q) : cPair (p - i) (q - i) = cPair p q := by
  unfold cPair
  rw [Nat.cast_sub hp, Nat.cast_sub hq]
  ring

theorem intw_eq_zero (X : ProvA) (h2 : admH2 X) (hD : DiscreteSeriesBlattner X) (h5 : admQ5 X)
    {p q r s : ℕ} (hrs : 1 ≤ r + s) (lam : Ix r s → ℚ) (hlam : IsParam lam) (θ : ℚ)
    (hsign : ∀ a, (θ < lam a → 0 ≤ shiftNu (cPair p q) (blattner lam) a) ∧
      (lam a ≤ θ → shiftNu (cPair p q) (blattner lam) a ≤ 0))
    (hno : ∀ μ, ¬ JointShape p q r s μ (blattner lam))
    (MM : GKMod p q) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ MM.V (X.ds r s lam).HK.V)
    (hf : IsIntw (X.fock p q r s) MM (X.ds r s lam).HK f) : f = 0 := by
  by_contra hf0

  have hAI := discrete_series_gk_admissible_irreducible X h5 hrs lam
  have hI : Intw MM (X.ds r s lam).HK f := (isIntw_iff (X.fock p q r s) MM _ f).1 hf
  obtain ⟨hfin, -, hcone⟩ := hD r s lam hlam

  have hex : ∃ v, IsHW (X.ds r s lam).HK.act (blattner lam) v := by
    have hne : hwSub (X.ds r s lam).HK.act (blattner lam) ≠ ⊥ := by
      intro h
      rw [h] at hfin
      simp at hfin
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨v, hv0, hv⟩

  have hmin : ∀ ν w, IsHW (X.ds r s lam).HK.act ν w →
      degW (cPair p q) (blattner lam) ≤ degW (cPair p q) ν :=
    GlobalTheory.T.degW_blattner_le_of_blattnerCone r s (X.ds r s lam).HK lam (cPair p q) θ hcone hsign

  obtain ⟨⟨μ, P, hPJ, hP1, hP2, hfP⟩, -⟩ :=
    GlobalTheory.T.fock_minimal_KType_second_member p q r s MM (X.ds r s lam).HK f hAI.2 hAI.1 hI hf0 (blattner lam) hex hmin

  have hbot := ((h2 p q r s).2.2.2.2.1 μ (blattner lam)).2 (hno μ)
  have hmem : P ∈ hwSub (X.fock p q r s).act1 μ ⊓ hwSub (X.fock p q r s).act2 (blattner lam) ⊓
      Submodule.span ℂ (X.fock p q r s).J := by
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hP1.2, hP2.2⟩, ?_⟩
    rw [J_eq (X.fock p q r s)]
    exact Submodule.subset_span hPJ
  rw [hbot] at hmem
  exact hP1.1 ((Submodule.mem_bot ℂ).1 hmem)

theorem no_map_smaller_source :
    ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → ArchimedeanRallisFifth X := by
  intro X _ h2 hD h5
  unfold ArchimedeanRallisFifth ARv DataAR DataARm
  constructor
  ·
    intro t al be ga de hd hne i hi1 hip hiq MM f hf
    have hA := hd.1
    have ht : 1 ≤ t := by
      unfold HypA at hA
      exact hA.1
    obtain ⟨-, -, hlam', -, hs'⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
    have hno := ((GlobalTheory.T.lowestType_not_jointShape_smaller_pairs t al be ga de hA i hi1).2.2 hne hip hiq).1
    refine intw_eq_zero X h2 hD h5 (by omega) (lamA' t al be ga de) hlam' ((t : ℚ) / 2) ?_ hno MM f hf
    rw [cPair_sub hip hiq]
    exact hs'
  ·
    intro t al be ga de hd hne i hi1 hip hiq MM f hf
    have hA := hd.1
    have ht : 1 ≤ t := by
      unfold HypA at hA
      exact hA.1
    obtain ⟨-, hlam', -, hs'⟩ := GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS t al be ga de hA
    have hno := ((GlobalTheory.T.lowestType_not_jointShape_smaller_pairs t al be ga de hA i hi1).2.2 hne hip hiq).2
    refine intw_eq_zero X h2 hD h5 (by omega) (lamM' t al be ga de) hlam' ((t : ℚ) / 2) ?_ hno MM f hf
    rw [cPair_sub hip hiq]
    exact hs'

end GlobalTheory.SmallerSource
