module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetOfInducedFiltration
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

theorem PositivityTheory.Geo.geometricLemmaFiltration : GlobalTheory.Published.GeometricLemmaFiltration :=
  fun k _ _ _ _ => GlobalTheory.CompanionTheory.GeoAssembly.jacquetOfInducedFiltration k
