module

public import Mathlib
public import Development.Core20Slim.GroundTheory.LocalFields.LocalArtinUniqueness
public import Development.Core20Slim.GroundTheory.LocalFields.LocalArtinFunctoriality
public import Development.Core20Slim.GroundTheory.LocalFields.LocalArtinTransport
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.SeparableDegree

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

section Main

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

end Main

section Functoriality

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {K' : Type*} [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

theorem isSepClosure_of_isSeparable (K K' Ω : Type*) [Field K] [Field K'] [Field Ω] [Algebra K K']
    [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω] [Algebra.IsSeparable K K'] [IsSepClosure K' Ω] :
    IsSepClosure K Ω :=
  ⟨IsSepClosure.sep_closed K', Algebra.IsSeparable.trans K K' Ω⟩



end Functoriality

end GroundTheory.LocalField
