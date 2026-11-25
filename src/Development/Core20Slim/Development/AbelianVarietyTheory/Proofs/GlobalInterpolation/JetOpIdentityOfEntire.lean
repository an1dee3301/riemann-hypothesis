module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SubDSharpInDeg
public import Formalism.CoboundaryTransfers.Statement
public import Formalism.LocalRingCardinality.DataArith
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.SharpRestriction.GrowthBounds.DataG
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H  GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.JetIdentity

open MvPolynomial

section Lin

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

omit [Fintype ι] in
theorem jetLin_add (J J' : (DVar ι a b →₀ ℕ) → K) : jetLin (J + J') = jetLin J + jetLin J' := by
  refine (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).ext fun m => ?_
  simp only [jetLin, LinearMap.add_apply, Module.Basis.constr_basis, Pi.add_apply, map_add (f := _)]

omit [Fintype ι] in
theorem jetLin_smul (c : K) (J : (DVar ι a b →₀ ℕ) → K) : jetLin (c • J) = c • jetLin J := by
  refine (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).ext fun m => ?_
  simp only [jetLin, LinearMap.smul_apply, Module.Basis.constr_basis, Pi.smul_apply, smul_monomial]

def jetOpL (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) :
    ((DVar ι a b →₀ ℕ) → K) →ₗ[K] (Formalism.L2.DIV.VV K lam →ₗ[K] Formalism.L2.DIV.VV K lam') where
  toFun J := jetOp lam lam' J n
  map_add' J J' := by
    ext1 F
    simp only [jetOp, jetMap, jetLin_add, LinearMap.comp_apply, LinearMap.add_apply, map_add (f := _)]
  map_smul' c J := by
    ext1 F
    simp only [jetOp, jetMap, jetLin_smul, LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]




end Lin

section An

variable {ι : Type} [Fintype ι] {a b : ℕ}



end An

end GlobalTheory.JetIdentity



end
