module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PVectorOrbitsFinite
public import Development.Core20Slim.Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerExtra
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineIndex
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

theorem LineIndexNeZero.proof (E W : Type*) [Field E] [NumberField E] [AddCommGroup W]
    [Module E W] : LineIndexNeZero.Statement E W :=
  _root_.UpperTheory.Reformulated.B.Gub1.proof E W

end GroundTheory.Heights₂.Heights.FiniteCovolume
