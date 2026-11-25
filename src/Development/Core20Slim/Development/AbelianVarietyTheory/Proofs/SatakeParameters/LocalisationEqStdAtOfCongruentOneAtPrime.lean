module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSpec
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Formalism.LocalToGlobal.Columns.Adelic
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementC
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Init.Core
public import Init.Data.Subtype.Basic
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col  Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU 
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CongStdLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F






variable {P : HeightOneSpectrum (𝓞 E)} {L : Submodule (𝓞 E) (Fin N → E)}











theorem mem_hatL_std_iff (z : Fin N → E ⊗[F] 𝔸) :
    z ∈ Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E N) ↔ ∀ i, z i ∈ Formalism.L2.Herm.intAf F E :=
  Formalism.L2.Col.mem_latS_std z




theorem hatL_eq_lamAf (L : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.Herm.hatL (F := F) L = Formalism.MainNotions.S.lamAf (F := F) L := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS Formalism.MainNotions.S.lamAf
  congr 1
  ext x
  simp

theorem incl_mem_hatL_iff (hL : L.FG) (hspan : Submodule.span E (L : Set (Fin N → E)) = ⊤) (u : Fin N → E) :
    (fun i => iA F E (u i)) ∈ Formalism.L2.Herm.hatL (F := F) L ↔ u ∈ L := by
  rw [hatL_eq_lamAf]
  exact GlobalTheory.AdelicLattice.incl_mem_iff (F := F) L hL hspan u











end GlobalTheory.CongStdLoc
