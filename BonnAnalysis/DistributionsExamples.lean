import Mathlib.Topology.Sequences
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order
import Mathlib.Order.Filter.Basic
import Mathlib.Init.Function
import BonnAnalysis.ConvergingSequences
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.UniformSpace.UniformConvergence
import BonnAnalysis.UniformConvergenceSequences
import BonnAnalysis.Distributions
import Mathlib
import Mathlib.Analysis.Convolution
--import Mathlib.Analysis.InnerProductSpace
-- import Mathlib.Order
-- noncomputable section
--open FourierTransform MeasureTheory Real


namespace MeasureTheory
open MeasureTheory
universe u v
open Order Set

open scoped Classical
open NNReal Topology
open Filter


open scoped Topology
open TopologicalSpace
noncomputable section
open Function
variable {V : Type u} {k : Type v} [NontriviallyNormedField k]
  [MeasurableSpace V] [NormedAddCommGroup V]  [NormedSpace k V] {Ω : Opens V}
class GoodEnoughAutom (k : Type v) [NontriviallyNormedField k]  [MeasurableSpace V] [NormedAddCommGroup V]  [NormedSpace k V] (Ω : Opens V) (Φ : V → V) where
  isLinear : IsLinearMap k Φ
  isSmooth : ContDiffOn k ⊤ Φ univ
  restToΩ : Φ '' Ω ⊆ Ω
  inj : Function.Injective Φ

  /-
  Issue : If test functions are supported inside Ω, then things like negation and shift have to send Ω to Ω
  -/
open GoodEnoughAutom
open 𝓓

def fromAutoOfV (Φ : V → V) [GoodEnoughAutom k Ω Φ] : 𝓓 k Ω →L[k] 𝓓 k Ω := by
  apply mk ; swap
  ·   intro ψ
      use ψ ∘ Φ
      · exact ContDiffOn.comp ψ.φIsSmooth (isSmooth Ω) (subset_rfl)
      · sorry
      · sorry
      --ψ.φHasCmpctSupport
  · constructor
    · intro φ ψ
      ext x
      rfl
    · sorry
    · sorry

def negation : V → V := fun x => -x
def Full (V : Type u) [TopologicalSpace V] : Opens V := ⟨ univ , isOpen_univ ⟩
instance : (GoodEnoughAutom k (Full V)) negation where
  isLinear := by sorry
  isSmooth := by sorry
  restToΩ := by sorry
  inj := by sorry



/--
        Issue: If φ ψ : V → k and are smooth on Ω , how to show that the derivative is additive outside Ω ?
        --/

def fderiv𝓓 (v : V) : (𝓓 k Ω) →L[k] 𝓓 k Ω := by
  let f : 𝓓 k Ω → 𝓓 k Ω := fun φ => ⟨ fun x => fderiv k φ x v , by sorry , by sorry , by sorry ⟩
  apply mk ; swap
  · exact f
  · constructor
    ·     intro φ ψ
          ext x
          by_cases p : x ∈ Ω ; swap
          · sorry
          · have : (fderiv k (fun y => φ.φ y + ψ.φ y) x) = (fderiv k φ.φ x) + (fderiv k ψ.φ x) := by
              apply fderiv_add
              · exact diffAt k Ω φ p
              · exact diffAt k Ω ψ p
            have obv : ((fderiv k (fun y => φ.φ y + ψ.φ y) x)) v = (fderiv k φ.φ x) v + (fderiv k ψ.φ x) v := by
              rw [this]
              rfl
            exact obv
    · sorry
    · constructor
      intro x a hx
      apply tendsTo𝓝
      constructor
      · obtain ⟨ K , hK ⟩ := hx.1
        use K
        constructor
        · exact hK.1
        · intro n
          trans (tsupport (x n).φ)
          · sorry
          · exact hK.2 n
      · intro l
        have : TendstoUniformlyOn (fun n ↦ iteratedFDeriv k (l+1) (x n).φ) (iteratedFDeriv k (l+1) (a).φ) atTop univ := hx.2 (l+1)
        let g : (V[×(l+1)]→L[k] k) → (V[×l]→L[k] k)  := fun φ => by sorry -- evaluation at v
        have hxg (x : 𝓓 k Ω)  :  iteratedFDeriv k l (f x).φ = g ∘ iteratedFDeriv k (l + 1) (x).φ := by sorry

        rw [hxg]
        have hxg :  (fun (n : ℕ) => iteratedFDeriv k l ((f ∘ x) n).φ) =
          fun (n : ℕ) => g ∘ (iteratedFDeriv k (l + 1) (x n).φ) := by
            ext1 n -- does not work because it ext's all params
            sorry -- exact hxg (x n) --help


        rw [hxg]


        apply UniformContPresUniformConvergence this g
        sorry

example (v : V) (φ : 𝓓 k Ω ) (T : 𝓓' k Ω ): (fderiv𝓓 v ° T) φ = T (fderiv𝓓 v φ) := by rfl
-- def reflection : 𝓓 k Ω → 𝓓 k Ω := fun ψ => ⟨ fun x => ψ (-x) , by sorry , by sorry ⟩
-- instance : AddHomClass reflection _ _ where

--notation "𝓓F" k V => 𝓓 k (Full V)
def reflection  : (𝓓 k (Full V)) →L[k] (𝓓 k V) := fromAutoOfV negation

notation:67 ψ "ʳ" => reflection ψ


structure LocallyIntegrableFunction (V : Type u) [MeasureSpace V] [NormedAddCommGroup V]  [NormedSpace ℝ V] where
   f : V → ℝ
   hf : MeasureTheory.LocallyIntegrable f
variable {V : Type u}  [MeasureSpace V]
   [NormedAddCommGroup V]  [NormedSpace ℝ V] {Ω : Open V}
instance  :  CoeFun (LocallyIntegrableFunction V) (fun _ => V → ℝ) where
  coe σ := σ.f
def Λ (f : LocallyIntegrableFunction V) : 𝓓' ℝ Ω := by
  apply mk ; swap
  · exact fun φ => ∫ v , f v * φ v
  · sorry
--instance : Coe (LocallyIntegrableFunction V) (𝓓 k Ω ) where
open Convolution
def shift (x : V) : 𝓓 ℝ Ω →L[ℝ] 𝓓 ℝ Ω := by
  apply mk ; swap
  · exact fun φ => ⟨ fun y => φ (y - x)  , by sorry , by sorry ⟩
  · constructor
    · sorry
    · sorry
    · sorry

def convolution𝓓 : (𝓓 ℝ Ω)[×2]→L[ℝ] 𝓓 ℝ Ω := by

  let c : MultilinearMap ℝ (fun (i : Fin 2) => 𝓓 ℝ Ω) (𝓓 ℝ  Ω) := ⟨
      fun φ  => ⟨ φ 0 ⋆ φ 1 , by sorry , by sorry ⟩,
      by sorry ,
      by sorry
    ⟩
  use c

/-
(𝓓 ℝ Ω)→L[ℝ] (𝓓 ℝ Ω) →L[ℝ] 𝓓 ℝ Ω :=
-/
    -- apply MultiLinearMap.mk ; swap
    -- · apply AddHom.mk ; swap
    --   intro φ ψ

    --   use φ ⋆ ψ -- (ContinuousLinearMap.mul k k)
    --   sorry
    --   sorry
    --   sorry

    -- · sorry

  sorry
def tF2 {X : Type u} (x y : X) : (Fin 2) → X
| 0 => x
| 1 => y


notation:67 φ " 𝓓⋆ " ψ => convolution𝓓 (tF2 φ ψ)
def curry (φ : 𝓓 ℝ Ω ) : 𝓓 ℝ Ω →L[ℝ] 𝓓 ℝ Ω := ContinuousMultilinearMap.toContinuousLinearMap convolution𝓓 (tF2 φ 0) 1
notation:67 T " °⋆ " φ => ( curry (reflection φ) ) ° T
example  (φ : 𝓓 ℝ Ω ) (T : 𝓓' ℝ Ω ) : ∀ ψ, (T °⋆ φ) ψ = T ( φʳ 𝓓⋆ ψ) := fun _ => rfl
theorem convolution𝓓'IsSmooth (ψ : 𝓓 ℝ Ω ) (T : 𝓓' ℝ Ω ) : ∃ ψ' , ContDiffOn ℝ ⊤ ψ'.f Ω ∧ (T °⋆ ψ) = Λ ψ' := by
  let ψ' : V → ℝ := fun x => by
    let ψ'' := shift x (reflection ψ)
    exact T ψ''
  use ⟨ ψ , by sorry ⟩
  constructor
  · sorry
  · ext φ
    simp


    sorry
