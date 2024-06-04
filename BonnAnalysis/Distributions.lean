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

universe u
open Order Set Filter
open Filter
open Manifold

open scoped Topology
noncomputable section
variable {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d))) (isOpenω : IsOpen Ω)
instance : ChartedSpace (EuclideanSpace ℝ (Fin d)) ℝ := by sorry
instance : ChartedSpace (EuclideanSpace ℝ (Fin d)) ↑Ω where
  atlas := by sorry
  mem_chart_source := by sorry
  chartAt := by sorry
  chart_mem_atlas := by sorry
structure 𝓓 where
  φ : Ω → ℝ
  φIsSmooth : Smooth (𝓡 d) (𝓡 1) φ
  φHasCmpctSupport : HasCompactSupport φ
instance :  CoeFun (𝓓 Ω) (fun _ => Ω → ℝ) where
  coe σ := σ.φ
instance : AddCommMonoid (𝓓 Ω) where
instance : Module ℝ (𝓓 Ω) where


instance : Topology.ConvergingSequences (𝓓 Ω) where
  seq := fun (a , x) =>
    ∃ K : Set Ω , IsCompact K ∧ ∀ n , mulTSupport (a n) ⊆ K ∧
    TendstoUniformlyOn (fun n => (a n).φ) x atTop univ
  seq_cnst := by sorry
  seq_diag := by sorry
  seq_sub := by sorry
def 𝓓' := (𝓓 Ω) →L[ℝ] ℝ
instance :  CoeFun (𝓓' Ω) (fun _ => 𝓓 ( Ω ) → ℝ ) where
  coe σ := by sorry
instance : Topology.ConvergingSequences (𝓓' Ω) where
  seq := fun (a , x) => ∀ φ : 𝓓 Ω , Tendsto (fun n => (a n) φ ) atTop (𝓝 (x φ))
  seq_cnst := by sorry
  seq_diag := by sorry
  seq_sub := by sorry
instance : TopologicalSpace (𝓓' Ω) := by -- should follow automatically
