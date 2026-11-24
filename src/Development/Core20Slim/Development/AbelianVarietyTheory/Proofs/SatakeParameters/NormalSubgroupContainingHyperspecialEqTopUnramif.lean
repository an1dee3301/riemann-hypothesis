module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetOfGLintDoubleCoset
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.UniformSpace.Cauchy

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormalHyp




open Formalism.UG in
theorem frame {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q n : ℕ}
    (hU : IsUnramInv ϖ σ q) {J : GL (Fin n) L} (hJ : J ∈ GLint (Fin n) (intL L))
    (hh : ∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) :
    ∃ P ∈ GLint (Fin n) (intL L), cT σ (P : Matrix (Fin n) (Fin n) L) * (J : Matrix (Fin n) (Fin n) L) * P = antiJ L n := by
  obtain ⟨U, rfl⟩ := hJ
  let c := GlobalTheory.UnramDoubleCoset.intConj hU.2.1
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hU.1 x)
  let ι := (intL L).subtype
  let B : Matrix (Fin n) (Fin n) (intL L) := U
  have hB : cT c B = B := by
    ext i j
    show σ ((B j i : intL L) : L) = (B i j : L)
    exact hh j i
  obtain ⟨p, hp⟩ := GlobalTheory.UnitaryDoubleCoset.exists_poly_norm hc (GlobalTheory.UnramDoubleCoset.exists_dvd_norm_sub_X hU) hB U.isUnit
  have hu : IsUnit B := U.isUnit
  have h2 : IsUnit (Polynomial.aeval B p) := isUnit_of_mul_isUnit_right (by rw [hp]; exact hu)
  obtain ⟨h, hh', eh⟩ := GlobalTheory.UnramDoubleCoset.exists_antiJ_frame hU n
  set K : GL (Fin n) L := bc ι h2.unit with hKdef
  have hK : (K : Matrix (Fin n) (Fin n) L) = (Polynomial.aeval B p).map ι := rfl
  have hJ : ((bc ι U : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = cT σ (K : Matrix (Fin n) (Fin n) L) * K := by
    rw [hK, GlobalTheory.UnitaryDoubleCoset.cT_map ι (c := c) (fun _ => rfl), ← Matrix.map_mul, hp]; rfl
  refine ⟨K⁻¹ * h, mul_mem (inv_mem ⟨_, rfl⟩) hh', ?_⟩
  rw [hJ, Units.val_mul, cT_mul, ← eh, Matrix.mul_one]
  have e1 : cT σ ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * cT σ (K : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← cT_mul, Units.mul_inv, cT_one]
  have e2 : (K : Matrix (Fin n) (Fin n) L) * ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv K
  calc cT σ (h : Matrix (Fin n) (Fin n) L) * cT σ ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (cT σ (K : Matrix (Fin n) (Fin n) L) * K) * (((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * h)
      = cT σ (h : Matrix (Fin n) (Fin n) L) * (cT σ ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * cT σ (K : Matrix (Fin n) (Fin n) L)) * ((K : Matrix (Fin n) (Fin n) L) * ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) * h := by
        simp only [Matrix.mul_assoc]
    _ = cT σ (h : Matrix (Fin n) (Fin n) L) * h := by rw [e1, e2, Matrix.mul_one, Matrix.mul_one]



end GlobalTheory.NormalHyp
