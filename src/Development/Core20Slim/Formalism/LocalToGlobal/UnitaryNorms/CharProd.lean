module

public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.Core20Slim.Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HeckeProd
public import Mathlib.Algebra.Field.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Host.HChar

variable {L : Type} [Field L] [NumberField L] (χ : HChar L)

theorem productRule : χ.ProductRule := hecke_product_rule L χ


end Formalism.L2.Host.HChar
