module

public import Formalism.LocalToGlobal.GlobalTheory.LinkTiesTh
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.CMQuasiPeriodConst
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroTranslateProduct
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs

@[expose] public section

noncomputable section

namespace Formalism.L2.Th1.F2

open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions

def IsLat (Λ : AddSubgroup ℂ) : Prop := ∃ L : PeriodPair, L.lattice.toAddSubgroup = Λ

def HasCM (d : ℕ) (Λ : AddSubgroup ℂ) : Prop := ∀ x ∈ Λ, F.cmTheta 1 d * x ∈ Λ


end Formalism.L2.Th1.F2
