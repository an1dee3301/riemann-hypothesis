module

public import Mathlib
public import Development.Core20Slim.Formalism.LocalToGlobal.InertKernelTheory.DefsSigma
public import Development.Core20Slim.Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
public import Development.Core20Slim.Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LamConjTheta0
public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CmAll
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.DedekindFactorK
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.ExistsTwoTorsionOffKernels
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.CMQuasiPeriodConst
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.DivMod.Bootstrap
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert.Sigma

namespace ChartWirtingerDerivatives

open NumberField Formalism.BasicNotions

theorem qbar_iff (x : ℂ) : x ∈ Formalism.MainNotions.TaylorLogMetric.Qbar ↔ IsAlgebraic ℚ x := mem_algebraicClosure_iff

theorem qbar_of_pow {x : ℂ} {n : ℕ} (hn : 0 < n) (h : x ^ n ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) : x ∈ Formalism.MainNotions.TaylorLogMetric.Qbar :=
  (qbar_iff x).2 (IsAlgebraic.of_pow hn ((qbar_iff _).1 h))

theorem nat_mem (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  have h : ((n : ℕ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := natCast_mem _ n
  simpa using h

theorem d_sq (D : D7) : Squarefree D.host.d := (D.host.hyp.2.1 : D.host.d.Prime).squarefree

theorem host_imagQuadratic_discriminant_mod_four (D : D7) : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega

theorem hasCMBy_curve (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (L : PeriodPair)
    (hL : L.lattice.toAddSubgroup = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) : Formalism.L2.Th1.CM.HasCMBy D.host.d L := by
  have hδ0 : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcc δ hδ
  obtain ⟨-, hCM⟩ := Formalism.L2.Th1.F2.lamOfLat D cc δ hcc.1 hδ0
  intro ω hω
  have h1 := hCM ω (by rw [← hL]; exact hω)
  rw [← hL] at h1
  have e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
    unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring
  rw [e]; exact h1

theorem disc_curve (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (L : PeriodPair)
    (hL : L.lattice.toAddSubgroup = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
  have hL' : (L.lattice : Set ℂ) = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ := by rw [← hL]; rfl
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L hL'
  have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  rw [← e2, ← e3]
  exact h

theorem weierstrass_invariants_algebraic : InvAlg := by
  intro D cc δ hcc hδ L hL
  have hdisc := disc_curve D cc δ hcc hδ L hL
  have hcm := hasCMBy_curve D cc δ hcc hδ L hL
  have hj : IsIntegral ℤ (Formalism.L2.Th1.CM.jInv L) := Formalism.L2.Th1.CM.cm1 D.host.d L (d_sq D) (host_imagQuadratic_discriminant_mod_four D) hcm
  have hjQ : Formalism.L2.Th1.CM.jInv L ∈ Formalism.MainNotions.TaylorLogMetric.Qbar :=
    (qbar_iff _).2 (hj.tower_top (A := ℚ)).isAlgebraic
  have hg2c : L.g₂ ^ 3 = Formalism.L2.Th1.CM.jInv L / 1728 := by
    unfold Formalism.L2.Th1.CM.jInv; rw [hdisc]; ring
  have h2 : L.g₂ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    refine qbar_of_pow (n := 3) (by norm_num) ?_
    rw [hg2c]; exact div_mem hjQ (nat_mem 1728)
  have h3sq : L.g₃ ^ 2 = (L.g₂ ^ 3 - 1) / 27 := by rw [← hdisc]; ring
  have h3 : L.g₃ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    refine qbar_of_pow (n := 2) (by norm_num) ?_
    rw [h3sq]
    exact div_mem (sub_mem (pow_mem h2 3) (one_mem _)) (nat_mem 27)
  exact ⟨h2, h3⟩

end ChartWirtingerDerivatives

namespace ChartWirtingerDerivatives

open PowerSeries


















open Formalism.L2.Th1.C (mvExp mvExp_add mvExp_neg mvExp_nsmul mvExp_mul_neg rescale_mvExp coeff_mvExp constantCoeff_mvExp)




end ChartWirtingerDerivatives

open ChartWirtingerDerivatives

theorem invAlg' : InvAlg := ChartWirtingerDerivatives.weierstrass_invariants_algebraic


end Formalism.L2.KerInert.Sigma
