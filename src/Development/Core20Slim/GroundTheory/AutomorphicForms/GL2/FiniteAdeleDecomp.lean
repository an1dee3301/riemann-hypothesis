module

public import Mathlib
public import Development.Core20Slim.GroundTheory.AutomorphicForms.GL2.GodementSectionFactor
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleMeasure
public import Development.Core20Slim.GroundTheory.LocalFields.Different

@[expose] public section

namespace GroundTheory.Automorphic.GodementSection

open NumberField IsDedekindDomain MeasureTheory Filter Topology GroundTheory.Global GroundTheory.LocalField
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise ValuativeRel

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

section AtS

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

def adeleAtS : FiniteAdeleRing (𝓞 K) K →+ ((v : S) → v.1.adicCompletion K) where
  toFun x v := x v.1
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem adeleAtS_apply (x : FiniteAdeleRing (𝓞 K) K) (v : S) : adeleAtS S x v = x v.1 := rfl
















variable {S}





end AtS

section Integrals

variable {S : Finset (HeightOneSpectrum (𝓞 K))}






end Integrals

end

end GroundTheory.Automorphic.GodementSection
