import Mathlib.Topology.Sequences
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order
import Mathlib.Order.Filter.Basic
import BonnAnalysis.ConvergingSequences
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib
--import Mathlib.Analysis.InnerProductSpace
-- import Mathlib.Order
-- noncomputable section
--open FourierTransform MeasureTheory Real


namespace MeasureTheory
open MaesureTheory
universe u
open Order Set Filter
open Filter
open Manifold


open scoped Topology
noncomputable section
variable {V : Type u} (k : Type u)
  [NontriviallyNormedField k] [NormedAddCommGroup V]  [NormedSpace k V] (Ω : Set V)-- (isOpenω : IsOpen Ω)


#eval Lean.versionString
structure 𝓓  where
  φ : V → k
  φIsSmooth : ContDiffOn k ⊤ φ Ω --⊤ φ
  φHasCmpctSupport : HasCompactSupport φ

instance  :  CoeFun (𝓓 k Ω) (fun _ => V → k) where
  coe σ := σ.φ
instance : AddCommMonoid (𝓓 k Ω ) where
instance : Module k (𝓓 k Ω) where


instance : ConvergingSequences (𝓓 k Ω) where
  seq := fun (a , x) =>
    ∃ K : Set Ω , IsCompact K ∧ ∀ n , mulTSupport (a n) ⊆ K ∧
    TendstoUniformlyOn (fun n => (a n).φ) x atTop univ --derivatives missing todo
  seq_cnst := by sorry
  seq_diag := by sorry
  seq_sub := by sorry
def 𝓓' := (𝓓 k Ω ) →L[k] k

instance :  CoeFun (𝓓' k Ω ) (fun _ => (𝓓 k Ω)  → k ) where
  coe σ := σ.toFun
instance : ConvergingSequences (𝓓' k Ω ) where
  seq := fun (a , x) => ∀ φ : 𝓓 k Ω , Tendsto (fun n => (a n) φ ) atTop (𝓝 (x φ))
  seq_cnst := by sorry
  seq_diag := by sorry
  seq_sub := by sorry
