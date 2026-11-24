module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.HeightExists

variable {D : D7} {n : ℕ}

theorem lower_eq_zero {p : G D n} (hp : p ∈ P D n) (i j : Fin n) :
    mat p (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0 := by
  have h := (hp (Pi.single (finSumFinEquiv (.inl j)) 1)).1 (by
    ext k
    have : (finSumFinEquiv (Sum.inr k : Fin n ⊕ Fin n)) ≠ finSumFinEquiv (.inl j) := by
      rw [Ne, finSumFinEquiv.apply_eq_iff_eq]; simp
    simp only [LinearMap.funLeft_apply, Pi.single_eq_of_ne this, Pi.zero_apply])
  have h2 := congrFun h i
  simp only [LinearMap.funLeft_apply, Matrix.mulVec_single_one, Pi.zero_apply] at h2
  exact h2

theorem blkA_mul {p q : G D n} (hq : q ∈ P D n) : blkA (mat (p * q)) = blkA (mat p) * blkA (mat q) := by
  ext i j
  have e : mat (p * q) = mat p * mat q := rfl
  simp only [e, blkA, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [lower_eq_zero hq, mul_zero, Finset.sum_const_zero, add_zero]

theorem blkA_one : blkA (mat (1 : G D n)) = 1 := by
  have e : mat (1 : G D n) = 1 := rfl
  rw [e, blkA, Matrix.submatrix_one_equiv, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]

def leviBlock : P D n →* GL (Fin n) (AE D) :=
  MonoidHom.toHomUnits ⟨⟨fun p => blkA (mat p.1), blkA_one⟩, fun p q => blkA_mul q.2⟩

theorem continuous_mat : Continuous (mat : G D n → Mx D (n + n) (n + n)) :=
  Units.continuous_val.comp (isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)).continuous

theorem continuous_leviBlock : Continuous (leviBlock (D := D) (n := n)) := by
  have hA : Continuous fun g : G D n => blkA (mat g) :=
    continuous_matrix fun i j => continuous_mat.matrix_elem _ _
  rw [Units.continuous_iff]
  refine ⟨hA.comp continuous_subtype_val, ?_⟩
  refine (hA.comp (continuous_subtype_val.comp continuous_inv)).congr fun p => ?_
  rw [← map_inv]; rfl

theorem continuous_detGL : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) (AE D) → (AE D)ˣ) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  rw [Units.continuous_iff]
  refine ⟨Units.continuous_val.matrix_det, (Units.continuous_coe_inv.matrix_det).congr fun g => ?_⟩
  rw [← map_inv]; rfl

theorem isCompact_K : IsCompact (K D n : Set (G D n)) :=
  haveI := isLattice_stdLattice (E := D.host.E) (n := n + n)
  isCompact_levelAll (isCMExt_host D) _ _ _

theorem isClosed_P : IsClosed (P D n : Set (G D n)) := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI := t2Space_tensorProduct_finiteExtension (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : (P D n : Set (G D n)) = ⋂ x ∈ upperHalf D n, ({g | (mat g).mulVec x ∈ upperHalf D n} ∩
      {g | (mat g⁻¹).mulVec x ∈ upperHalf D n}) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, SetLike.mem_coe]
    refine ⟨fun h x hx => ⟨(h x).1 hx, ((P D n).inv_mem h x).1 hx⟩, fun h x => ⟨fun hx => (h x hx).1, fun hx => ?_⟩⟩
    have := (h _ hx).2
    change (mat g⁻¹).mulVec ((mat g).mulVec x) ∈ _ at this
    rwa [Matrix.mulVec_mulVec, show mat g⁻¹ * mat g = mat (g⁻¹ * g) from rfl, inv_mul_cancel,
      show mat (1 : G D n) = 1 from rfl, Matrix.one_mulVec] at this
  have hU : IsClosed (upperHalf D n : Set (Fin (n + n) → AE D)) :=
    isClosed_eq (f := fun (x : Fin (n + n) → AE D) (i : Fin n) => x (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)))
      (g := fun _ => 0) (continuous_pi fun i => continuous_apply _) continuous_const
  rw [this]
  exact isClosed_biInter fun x _ => (hU.preimage (continuous_mat.matrix_mulVec continuous_const)).inter
    (hU.preimage ((continuous_mat.comp continuous_inv).matrix_mulVec continuous_const))

end GlobalTheory.StdUnn.HeightExists

namespace GlobalTheory.StdUnn


open HeightExists in
theorem exists_height : ∀ (D : D7) (n : ℕ), ∃ H : G D n → ℝ≥0, IsHeight H := by
  intro D n
  let δ : P D n →* ℝ≥0 := (absA D).comp (Matrix.GeneralLinearGroup.det.comp leviBlock)
  have hc : Continuous δ := continuous_absE.comp (continuous_detGL.comp continuous_leviBlock)
  haveI := t2Space_adeleRing' (F := D.host.F)
  have ht := triv_of_isCompact (δ := δ) isClosed_P hc isCompact_K
  refine ⟨iwAbs δ (K D n), fun p hp a ha k hk => ?_⟩
  rw [show a = leviBlock (D := D) (n := n) ⟨p, hp⟩ from Units.ext ha.symm]
  exact iwAbs_mul_of_triv ht ⟨p, hp⟩ hk

end GlobalTheory.StdUnn

end
