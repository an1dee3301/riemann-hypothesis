module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.FglChordFactor
public import Development.Core20Slim.Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AddIntG
public import Development.Core20Slim.Formalism.PeriodIntegrals.AddIntG
public import Init.Prelude
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

noncomputable section

open Classical

namespace PI.FglChordFactor.Wk

theorem isWq_bridge {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h : IsWq W wq) : PI.AddIntG.IsWq W wq := h

end PI.FglChordFactor.Wk
