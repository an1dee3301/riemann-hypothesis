module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDarbouxCoordinatesCompareStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterAlmostUnramifiedStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedByElementaryStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChange

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]



variable [NumberField F]






end GlobalTheory.SympChange

