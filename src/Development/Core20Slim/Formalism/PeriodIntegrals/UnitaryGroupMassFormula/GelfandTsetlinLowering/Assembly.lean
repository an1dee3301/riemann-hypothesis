module

public import Development.Core20Slim.Formalism.PeriodIntegrals.GTLower
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTBranch
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTDefs
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem ioIntegral_of (hZ : CapelliZ) (hL : LiftMod) (hV : ZScalarVanish) : IoIntegral := by
  intro n N h lam sg hI io0 hE hx hW s hs
  obtain ⟨Z, hZi, hZa⟩ := hZ n N h lam sg hI
  obtain ⟨m, hm, hd⟩ := hL n N h lam sg hI io0 hE hx hW s hs
  obtain ⟨f', hf', hZf⟩ := hZi m hm
  refine ⟨f', hf', ?_⟩
  have hsC : MvPolynomial.map (Int.castRingHom ℂ) s ∈ nablaSq ℂ n sg :=
    Formalism.GradedWeylDivisibility.dualWeylMap ℤ ℂ (Int.castRingHom ℂ) n n sg.natW s hs
  have hO : OtherPart h lam sg ≤ LinearMap.ker Z := by
    unfold OtherPart
    refine iSup_le fun mu => iSup_le fun hmu => iSup_le fun hne => iSup_le fun hw =>
      iSup_le fun φ => iSup_le fun hφ => ?_
    rintro _ ⟨t, ht, rfl⟩
    rw [LinearMap.mem_ker, hZa mu hmu φ hφ t ht, hV n N h lam sg mu hI hmu hne hw, Int.cast_zero, zero_smul]
  have h0 := hO hd
  rw [LinearMap.mem_ker, map_sub, hZf, hZa sg hI io0 hE _ hsC] at h0
  have hz : zScalar h lam sg sg = cBr h lam sg := rfl
  rw [hz] at h0
  rw [map_smul]
  exact (sub_eq_zero.mp h0).symm

theorem sqAct_smul {k : ℕ} (mu : DomWeight k) (g : GL (Fin k) ℂ) (c : ℂ)
    (x : MvPolynomial (Fin k × Fin k) ℂ) : sqAct ℂ k mu g (c • x) = c • sqAct ℂ k mu g x := by
  rw [sqAct, sqAct, map_smul, smul_comm]

theorem gTLower_of_steps (hN : Numbers) (hX : XiFacts) (hE : IoExists) (hP4 : IoIntegral)
    (hA : AdjointBr) (hB : BrIntegral) : PI.GTLower := by
  intro n N h lam sg hI
  obtain ⟨hc0, hcB, hdeg⟩ := hN n N h lam sg hI
  obtain ⟨hxi0, -⟩ := hX n N h lam sg hI
  obtain ⟨io0, ⟨hE1, hE2⟩, hx, hW⟩ := hE n N h lam sg hI
  let c : ℂ := ((cBr h lam sg : ℤ) : ℂ)
  let io := c • io0
  have hio : ∀ x, io x = c • io0 x := fun x => rfl
  have I2 : ∀ s ∈ nablaSq ℂ n sg, io s ∈ nablaSq ℂ N lam := fun s hs =>
    Submodule.smul_mem _ _ (hE1 s hs)
  have I3 : ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n sg,
      io (sqAct ℂ n sg g s) = sqAct ℂ N lam (embGL ℂ n N h g) (io s) := by
    intro g s hs
    rw [hio, hio, hE2 g s hs, sqAct_smul]
  have I4 : io (extremal ℂ n sg) = c • xi ℂ h lam sg := by rw [hio, hx]
  have I5 : LastWeight lam sg io := by
    intro a s hs
    rw [hio, sqAct_smul, hW a s hs, smul_comm]
  have I1 : ∀ s ∈ nablaSq ℤ n sg, ∃ f ∈ nablaSq ℤ N lam,
      io (MvPolynomial.map (Int.castRingHom ℂ) s) = MvPolynomial.map (Int.castRingHom ℂ) f := by
    intro s hs
    obtain ⟨f, hf, hf'⟩ := hP4 n N h lam sg hI io0 ⟨hE1, hE2⟩ hx hW s hs
    exact ⟨f, hf, by rw [hio, ← map_smul]; exact hf'⟩
  obtain ⟨I6, br, hrest, hT⟩ := hA n N h lam sg hI io ⟨I2, I3⟩ I4 I5
  have B1 := hB n N h lam sg hI io br I1 I2 hrest.1 hT
  exact ⟨hc0, hcB, hxi0, hdeg, io, br, ⟨I1, I2, I3, I4, I5, I6⟩, ⟨B1, hrest⟩, hT⟩

end PI.WGL
