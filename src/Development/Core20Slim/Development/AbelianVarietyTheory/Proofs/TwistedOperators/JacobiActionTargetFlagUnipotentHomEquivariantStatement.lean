module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionTargetFlagUnipotentHomEquivariant
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_action_target_flag_unipotent_hom_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (T T₀ S : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (y : Mx D S.rank ρ), (∀ u ∈ UX D ρ, y ⬝ u.1 = y) → (∀ b c, cenT d S y (d.nB b * d.nC c) = d.qT S c y) ∧ (∀ n ∈ flagN d, ∀ n' ∈ flagN d, ptT d S y (n * n') = ptT d S y n + ptT d S y n' ∧ cenT d S y (n * n') = cenT d S y n + cenT d S y n' + symplOH S T₀ (ptT d S y n) (ptT d S y n') ∧ ∀ f, jacT ψ d S y (n * n') f = jacT ψ d S y n (jacT ψ d S y n' f)) ∧ (∀ n ∈ flagN d, ∀ u ∈ UX D ρ, jacT ψ d S y (n * d.levi u) = jacT ψ d S y n) ∧ ∀ n g, ptT d S y (d.emb0 g * n * (d.emb0 g)⁻¹) = actO S T₀ 1 g (ptT d S y n) ∧ cenT d S y (d.emb0 g * n * (d.emb0 g)⁻¹) = cenT d S y n := by
  first | exact @GlobalTheory.MixPer.jacT_hom | exact GlobalTheory.MixPer.jacT_hom | (intros; apply GlobalTheory.MixPer.jacT_hom <;> assumption)
