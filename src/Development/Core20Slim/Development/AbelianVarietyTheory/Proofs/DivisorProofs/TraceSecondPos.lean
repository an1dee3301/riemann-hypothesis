module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.RouteBigVertexKernelProductEqConstMulThetaKernel
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedHermitianFormQuadSumEqTrace
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RouteCoordsW

open GlobalTheory.RouteCoords GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation

theorem trace_second_pos {A : Type} [CommRing A] (c : A →+* A) {n b : ℕ} (hc : ∀ z, c (c z) = z) (ξ : A) (hξ : c ξ = -ξ)
    (g : Matrix (Fin n) (Fin n) A) (p pi : Matrix (Fin b) (Fin b) A) (hg : (g.map c)ᵀ = g) (hp : (p.map c)ᵀ = p)
    (hpi : pi * p = 1) (Z Z' : Matrix (Fin n) (Fin b) A) :
    c (ξ * (pi * ((-(Z'.map c * p)).map c)ᵀ * g * (-(Z.map c * p))).trace) =
      -(ξ * (Z * pᵀ * (Z'.map c)ᵀ * gᵀ).trace) := by
  rw [← trace_second c hc ξ hξ g p pi hg hp hpi Z Z', ← map_neg, ← mul_neg, ← trace_neg]
  congr 3
  simp only [Matrix.neg_mul, neg_neg]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.RouteCoordsW
