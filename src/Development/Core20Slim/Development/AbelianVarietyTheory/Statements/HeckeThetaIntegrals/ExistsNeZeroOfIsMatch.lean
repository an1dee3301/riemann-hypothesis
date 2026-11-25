module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemMulAAOfTrace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnThetaDefinite
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.ExistsHaarFundDom
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LowVanishFockOfLowVanish
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Defs.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.SquareSt.Model

variable {D : D7}

theorem exists_isWeil (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (ε : Bool) (M X : HSp D) {χ χ' : (AE D)ˣ →* Circle} (h1 : IsHeckeChar D χ) (h2 : IsHeckeChar D χ') (r1 : ResEta D χ M.rank)
    (r2 : ResEta D χ' X.rank) : ∃ ω, IsWeil ψ ε M X χ χ' ω := by
  obtain ⟨ω', hω'⟩ := hW D ψ (sgn ε M) X χ χ' hψ h1 h2 r1 r2
  refine ⟨ω'.comp ((ofSgn ε M).symm.toMonoidHom.prodMap (MonoidHom.id (GA D X))), ?_⟩
  have e : GlobalTheory.Grid.WRep.toSgn (S := M) (T := X) ε
      (ω'.comp ((ofSgn ε M).symm.toMonoidHom.prodMap (MonoidHom.id (GA D X)))) = ω' := by
    ext x : 1
    rcases x with ⟨g, k⟩
    simp [GlobalTheory.Grid.WRep.toSgn]
  unfold GlobalTheory.Grid.IsWeil
  rw [e]
  exact hω'

private theorem isHeckeChar_div' {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') :
    IsHeckeChar D (χ / χ') := by
  refine ⟨?_, fun x => ?_⟩
  · rw [div_eq_mul_inv]
    exact h.1.mul h'.1.inv
  · rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem exists_weil_of_isTriple (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) {W W₁ X : HSp D} {α β : (AE D)ˣ →* Circle} (h : IsTriple W W₁ X α β) :
    (∃ ωA, IsWeil ψ true W X β (β / α) ωA) ∧ ∃ ωB, IsWeil ψ false W₁ X α (α / β) ωB := by
  refine ⟨exists_isWeil hW hψ true W X h.hecB (isHeckeChar_div' h.hecB h.hecA) h.resB ?_,
    exists_isWeil hW hψ false W₁ X h.hecA (isHeckeChar_div' h.hecA h.hecB) h.resA ?_⟩
  · rw [div_eq_mul_inv, h.rank]
    exact Formalism.L2.Theta.resEta_mul h.resB (Formalism.L2.Theta.resEta_inv h.resA)
  · rw [div_eq_mul_inv, h.rank, add_comm]
    exact Formalism.L2.Theta.resEta_mul h.resA (Formalism.L2.Theta.resEta_inv h.resB)

end GlobalTheory.SquareSt.Model

end
