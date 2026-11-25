module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLatticeDenominatorHeightBoundProof
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NormInfSubmultiplicativeLeAdelicHeight
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

noncomputable section

namespace GlobalTheory.HolDict.ShortVec

section Coord

open scoped TensorProduct

variable {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] {m : ℕ}

theorem exists_common_denom {ι : Type} [Fintype ι] (R : Subring A) (x : ι → A)
    (h : ∀ i, ∃ d : ℕ, 0 < d ∧ (d : A) * x i ∈ R) : ∃ d : ℕ, 0 < d ∧ ∀ i, (d : A) * x i ∈ R := by
  classical
  choose n h0 h1 using h
  refine ⟨∏ i, n i, Finset.prod_pos fun i _ => h0 i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact R.mul_mem (natCast_mem R _) (h1 i)


end Coord

section Arith

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

variable (F : Type) [Field F] [NumberField F]

def intRing : Subring (Af F) :=
  ⨅ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F).toSubring.comap (evalV F v).toRingHom

variable {F}

theorem mem_intRing {a : Af F} : a ∈ intRing F ↔ ∀ v, ‖evalV F v a‖ ≤ 1 := by
  rw [intRing, Subring.mem_iInf]
  exact forall_congr' fun v => (Valued.toNormedField.norm_le_one_iff (x := evalV F v a)).symm

theorem exists_denom_adele (a : Af F) : ∃ d : ℕ, 0 < d ∧ (d : Af F) * a ∈ intRing F := by
  have hf : (Function.mulSupport fun v => max 1 ‖evalV F v a‖₊).Finite := by
    refine (Filter.eventually_cofinite.1 a.2).subset fun v hv hv' => hv (max_eq_left ?_)
    exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 hv'
  obtain ⟨d, hd, -, h⟩ := GlobalTheory.SmoothForms.denom_global _ (fun v => le_max_left _ _) hf
  refine ⟨d, hd, mem_intRing.2 fun v => ?_⟩
  rw [map_mul, map_natCast]
  exact h v _ (le_max_right _ _)


variable {E : Type} [Field E] [NumberField E] [Algebra F E] {m : ℕ}


end Arith

section Adelic

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}



def finPr (D : D7) : AF D.host.F ⊗[D.host.F] D.host.E →+* Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom







theorem exists_denom_le_height (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (g : GA D V) :
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ height θ V g ∧
      ∀ i j k, (d : Af D.host.F) * finCoord D (finMat D.sp.cm.sig V.gram g i j) k ∈ intRing D.host.F := by
  obtain ⟨d₁, hd₁, hle, hint⟩ := GlobalTheory.SmoothForms.denom_global (fun v => finHt V v g) (fun v => le_max_left _ _)
    (finHt_mulSupport_finite V g)
  have hH : (d₁ : NNReal) ≤ height θ V g :=
    hle.trans (le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => le_max_left _ _))
  refine ⟨d₁, hd₁, by exact_mod_cast hH, fun i j k => mem_intRing.2 fun v => ?_⟩
  have h1 : ‖evalV D.host.F v (finCoord D (finMat D.sp.cm.sig V.gram g i j) k)‖₊ ≤ finHt V v g :=
    (Finset.le_sup (f := fun p : Fin V.rank × Fin V.rank × Fin (Module.finrank D.host.F D.host.E) =>
      ‖evalV D.host.F v (finCoord D (finMat D.sp.cm.sig V.gram g p.1 p.2.1) p.2.2)‖₊)
      (Finset.mem_univ (i, j, k))).trans ((le_max_left _ _).trans (le_max_right _ _))
  rw [map_mul, map_natCast]
  exact hint v _ h1






end Adelic

end GlobalTheory.HolDict.ShortVec

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict


end GlobalTheory.HolDict

end
