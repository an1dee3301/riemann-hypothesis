module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentRealisedOnAdelicSchwartz
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympUnip

open GlobalTheory.SympChange GlobalTheory.AdelicSvNQuad GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic

section Ring

variable {R κ : Type} [CommRing R] [Fintype κ]







end Ring

variable {F : Type} [Field F] [NumberField F]









end GlobalTheory.SympUnip

end
