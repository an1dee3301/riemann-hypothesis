module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.HermitianLattices.StatementLat
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianSelfDualLatticeSpace_form_hermitian_nondeg_unimodular : ∀ (D : D7) (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (n : ℕ) (X : Spc D.host.F D.host.E n) (r s : ℕ), X.IsHerm D.sp.cm.sig B r s →
      (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).IsSymm ∧ (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).Nondegenerate ∧
        Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ) X.L := by
  first | exact @GlobalTheory.WeilSchrodingerHerm.main | exact GlobalTheory.WeilSchrodingerHerm.main | (intros; apply GlobalTheory.WeilSchrodingerHerm.main <;> assumption)
