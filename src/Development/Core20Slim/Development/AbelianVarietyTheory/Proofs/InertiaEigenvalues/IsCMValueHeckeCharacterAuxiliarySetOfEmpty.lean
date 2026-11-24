module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsValueTiedOfIsToricElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactorsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLNeZeroNat
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.HeckeGal GlobalTheory.ToricDenom GlobalTheory.ToricDistribution
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (lamF upIdele)

namespace GlobalTheory.ToricRational

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

section Core




variable {R : Ranks} {H : Host R} {I : Type} [Fintype I] {φ : I → H.E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF H.E)} {χ : HChar H.E}

theorem condQ_ne_bot {E : Type} [Field E] [NumberField E] {𝔣 : Ideal (OF E)} (h : 𝔣 ≠ ⊥) (Q : Finset (HeightOneSpectrum (OF E))) :
    condQ 𝔣 Q ≠ ⊥ := mul_ne_zero h (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)





end Core

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}



end Record

end GlobalTheory.ToricRational
