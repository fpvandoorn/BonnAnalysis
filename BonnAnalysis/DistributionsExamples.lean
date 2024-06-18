import Mathlib.Topology.Sequences
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order
import Mathlib.Order.Filter.Basic
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
open MaesureTheory
universe u v
open Order Set Filter
open Filter
open scoped Classical
open NNReal Topology


open scoped Topology
noncomputable section
variable {V : Type u} {k : Type v} [MeasurableSpace V]
  [NontriviallyNormedField k] [NormedAddCommGroup V]  [NormedSpace k V] {Ω : Open V}
class IsSeqCtsLinearMap
  {X : Type u} [ConvergingSequences X] [AddCommMonoid X] [Module k X]
  {M : Type* } [TopologicalSpace M] [AddCommGroup M] [Module k M]
 (f : X → M) where
  isAdd : ∀ x y, f (x + y) = f x + f y
  isSmUl : ∀ (c : k) (x), f (c • x) = c • f x
  isSeqCts : SeqContinuous' f
def mk  {M : Type* } [TopologicalSpace M] [AddCommGroup M] [Module k M]
  (T : 𝓓 k Ω → M) (hT : IsSeqCtsLinearMap T) := by
  -- (hT2 : IsLinearMap k T) (hT : SeqContinuous' T) : 𝓓 k Ω →L[k] M := by
  use ⟨ ⟨ T ,hT2.map_add ⟩ , hT2.map_smul ⟩
  apply continuous_of_SeqContinuous


/--
        Issue: If φ ψ : V → k and are smooth on Ω , how to show that the derivative is additive outside Ω ?
        --/

def fderiv𝓓 (v : V) : (𝓓 k Ω) →L[k] 𝓓 k Ω := by
  apply mk ; swap
  · exact fun φ => ⟨ fun x => fderiv k φ x v , by sorry , by sorry ⟩
  · constructor
    ·     intro φ ψ
          ext x
          by_cases p : x ∈ Ω.subset ; swap
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
  use f
  have : SeqContinuous' f := by
    constructor
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
      have hxg :  (fun (n : ℕ) => iteratedFDeriv k l ((⇑f ∘ x) n).φ) =
        fun (n : ℕ) => g ∘ (iteratedFDeriv k (l + 1) (x n).φ) := by
          ext n -- does not work because it ext's all params
          sorry -- exact hxg (x n) --help


      rw [hxg]


      apply UniformContPresUniformConvergence this g
      sorry
  apply continuous_of_SeqContinuous
example (v : V) (φ : 𝓓 k Ω ) (T : 𝓓' k Ω ): (fderiv𝓓 v ° T) φ = T (fderiv𝓓 v φ) := by rfl
-- def reflection : 𝓓 k Ω → 𝓓 k Ω := fun ψ => ⟨ fun x => ψ (-x) , by sorry , by sorry ⟩
-- instance : AddHomClass reflection _ _ where
def reflection  : 𝓓 k Ω →L[k] 𝓓 k Ω := by
  let c : 𝓓 k Ω →ₗ[k] 𝓓 k Ω  := by
    apply LinearMap.mk ; swap
    · apply AddHom.mk ; swap
      intro ψ
      exact ⟨ fun x => ψ (-x) , by sorry , by sorry ⟩
      intro φ ψ
      rfl

    · sorry --
  use c
  have : SeqContinuous' c := by sorry
  apply continuous_of_SeqContinuous
notation:67 ψ "ʳ" => reflection ψ

variable {V : Type u}  [MeasureSpace V]
   [NormedAddCommGroup V]  [NormedSpace ℝ V] {Ω : Open V}

def Λ (f : V → k) (hf : MeasureTheory.LocallyIntegrable f) : 𝓓' ℝ Ω := by

  apply LinearMap.mk ; swap
    · apply AddHom.mk ; swap
      · exact fun φ =>
open Convolution
def shift (x : V) : 𝓓 ℝ Ω →L[ℝ] 𝓓 ℝ Ω := by
  let c :  𝓓 ℝ Ω →ₗ[ℝ] 𝓓 ℝ Ω:= by
    apply LinearMap.mk ; swap
    apply AddHom.mk ; swap
    intro φ
    · exact ⟨ fun y => φ (y - x)  , by sorry , by sorry ⟩
    · sorry
    · sorry

  use c
  sorry
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
