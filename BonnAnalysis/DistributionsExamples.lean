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
def Full (V : Type u) [TopologicalSpace V] : Opens V := ⟨ univ , isOpen_univ ⟩
--def squareOpen {V : Type u} [TopologicalSpace V]  (Ω : Opens V) : Opens (V × V) := ⟨ Ω ×ˢ  Ω , by sorry ⟩
abbrev 𝓓F  (k : Type v) (V : Type u) [NontriviallyNormedField k]
  [MeasurableSpace V] [NormedAddCommGroup V]  [NormedSpace k V]  := 𝓓 k (Full V)
abbrev 𝓓'F  (k : Type v) (V : Type u) [NontriviallyNormedField k]
  [MeasurableSpace V] [NormedAddCommGroup V]  [NormedSpace k V]  := 𝓓' k (Full V)
class GoodEnoughAutom (k : Type v) (V : Type u)[NontriviallyNormedField k]  [MeasurableSpace V] [NormedAddCommGroup V]  [NormedSpace k V] (Φ : V → V) where
  isLinear : IsLinearMap k Φ
  --IsInjective : Function.Injective Φ
  IsProper : IsProperMap Φ
  isSmooth : ContDiff k ⊤ Φ

  --restToΩ : Φ '' Ω ⊆ Ω
  inj : Function.Injective Φ
variable {V : Type u} {k : Type v} [NontriviallyNormedField k]
  [MeasurableSpace V] [NormedAddCommGroup V]  [NormedSpace k V] {Ω : Opens V}
  /-
  Issue : If test functions are supported inside Ω, then things like negation and shift have to send Ω to Ω
  -/
open GoodEnoughAutom
open 𝓓
lemma supportfromAutoOfV (Φ : V → V) [GoodEnoughAutom k V Φ] (ψ : 𝓓F k V) : tsupport (ψ ∘ Φ) ⊆ Φ ⁻¹' (tsupport ψ ) := by

  have ( A : Set V ) : closure (Φ ⁻¹' (A)) ⊆ Φ ⁻¹' (closure A) := by
    apply Continuous.closure_preimage_subset
    apply ContDiff.continuous (𝕜:=k) (isSmooth)
  apply this (ψ ⁻¹' {x | x ≠ 0})


@[simp] def fromAutoOfV (Φ : V → V) [GoodEnoughAutom k V Φ] : 𝓓F k V →L[k] 𝓓F k V := by
  apply mk ; swap
  ·   intro ψ
      use ψ ∘ Φ
      · exact ContDiffOn.comp ψ.φIsSmooth (by rw [contDiffOn_univ] ; exact  isSmooth) (subset_rfl)
      · apply IsCompact.of_isClosed_subset ; swap
        exact isClosed_tsupport (ψ.φ ∘ Φ)
        swap
        · exact supportfromAutoOfV (k:=k) Φ ψ
        · apply IsProperMap.isCompact_preimage
          apply (IsProper (k:=k))
          exact (ψ.φHasCmpctSupport)
      · exact fun ⦃a⦄ a ↦ trivial
      --ψ.φHasCmpctSupport
  · constructor
    · intro φ ψ
      ext x
      rfl
    · intro c φ
      ext x
      rfl
    · constructor
      intro φ φ0 hφ
      obtain ⟨ ⟨ K , hK⟩  ,hφ ⟩ := hφ
      apply tendsTo𝓝
      constructor
      · use Φ ⁻¹' K
        constructor
        · apply IsProperMap.isCompact_preimage
          apply (IsProper (k:=k))
          exact hK.1
        · intro n
          trans
          · exact supportfromAutoOfV (k:=k) Φ (φ n)
          · apply Set.monotone_preimage
            exact hK.2 n

      · intro l
        sorry

@[simp] def reflection' : V → V := fun x => -x
@[simp] def shift' (x : V) : V → V := fun y => y - x

instance : (GoodEnoughAutom k V) reflection' where
  isLinear := by sorry
  isSmooth := by sorry
  IsProper := by sorry
  --restToΩ := by sorry
  inj := by sorry

instance (v : V) :  (GoodEnoughAutom k V) (shift' v) where
  isLinear := by sorry
  isSmooth := by sorry
  IsProper := by sorry
  --restToΩ := by sorry
  inj := by sorry


/--
        Issue: If φ ψ : V → k and are smooth on Ω , how to show that the derivative is additive outside Ω ?
        --/
def δ : 𝓓' k Ω := mk k (fun φ => φ 0) (by sorry)
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



@[simp] def reflection  : 𝓓F k V →L[k] (𝓓F k V) := fromAutoOfV reflection'


notation:67 ψ "ʳ" => reflection ψ

---------- the rest deals with real numbers
variable  (V : Type u) [MeasureSpace V] [NormedAddCommGroup V]  [NormedSpace ℝ V]
structure LocallyIntegrableFunction where
   f : V → ℝ
   hf : MeasureTheory.LocallyIntegrable f


def intSm (φ : V → 𝓓F ℝ V)  (hφ : HasCompactSupport (fun x y => φ y x)) : 𝓓F ℝ V := ⟨ fun y => ∫ x , φ y x , by sorry , by sorry , by sorry⟩
--ContinuousLinearMap.integral_comp_comm PROBLEM: 𝓓F ℝ V is not NormedAddGroup so we cant apply
lemma FcommWithIntegrals (φ : V → 𝓓F ℝ V)  (hφ : HasCompactSupport (fun x y => φ y x)) (T : 𝓓'F ℝ V) : T (intSm V φ hφ) =  ∫ x : V ,  T (φ x)  := by
  symm
  -- have : Integrable φ := by sorry
  -- rw [ContinuousLinearMap.integral_comp_comm T.1]



  sorry
--def fromCurrying (φ : V → 𝓓F ℝ V)  (hφ : HasCompactSupport (fun x y => φ y x)) : 𝓓F ℝ (V × V ) := ⟨ fun x => φ x.1 x.2 , by sorry  , by sorry ,   fun ⦃a⦄ a ↦ trivial ⟩ -- todo
variable {V : Type u}  [MeasureSpace V]
   [NormedAddCommGroup V]  [NormedSpace ℝ V] {Ω : Opens V}
instance : Coe ( 𝓓F ℝ V) (LocallyIntegrableFunction V) where
  coe φ := ⟨ φ , by sorry ⟩

--def 𝓓kSquareCurry (φ : 𝓓 ℝ (squareOpen Ω )) (x : Ω ) : 𝓓 ℝ Ω := ⟨ fun y => φ ( x, y) , by sorry , by sorry , by sorry⟩
--def intSm (φ : 𝓓 ℝ (squareOpen Ω )) : 𝓓 ℝ Ω := ⟨ fun y => ∫ x , φ ( x, y) , by sorry , by sorry , by sorry⟩
--lemma FcommWithIntegrals [MeasureSpace Ω] (φ : 𝓓 ℝ (squareOpen Ω )) (T : 𝓓' ℝ Ω) :  ∫ x , T (𝓓kSquareCurry φ x) = T (intSm φ) := by sorry
--def transport (φ : 𝓓 k Ω) {ψ : V → ℝ} (p : φ = ψ) : 𝓓 k Ω
instance  :  CoeFun (LocallyIntegrableFunction V) (fun _ => V → ℝ) where
  coe σ := σ.f
@[simp] def Λ (f : LocallyIntegrableFunction V) : 𝓓' ℝ Ω := by
  apply mk ; swap
  · exact fun φ => ∫ v , f v * φ v
  · sorry
--instance : Coe (LocallyIntegrableFunction V) (𝓓 k Ω ) where
open Convolution

@[simp] def shift (x : V) : 𝓓F ℝ V →L[ℝ] 𝓓F ℝ V := fromAutoOfV (shift' x)

def convolution𝓓Mult : (𝓓 ℝ Ω)[×2]→L[ℝ] 𝓓 ℝ Ω := by

  let c : MultilinearMap ℝ (fun (i : Fin 2) => 𝓓 ℝ Ω) (𝓓 ℝ  Ω) := ⟨
      fun φ  => ⟨ φ 0 ⋆ φ 1 , by sorry , by sorry, by sorry ⟩,
      by sorry ,
      by sorry
    ⟩
  use c
  sorry

-- @[simp] def tF2 {X : Type u} (x y : X) : (Fin 2) → X
-- | 0 => x
-- | 1 => y

@[simp] def convWith ( φ : 𝓓 ℝ Ω) : (𝓓 ℝ Ω) →L[ℝ] 𝓓 ℝ Ω := mk ℝ (fun ψ => ⟨ φ ⋆ ψ , by sorry , by sorry , by sorry ⟩) sorry





notation:67 φ " 𝓓⋆ " ψ => convWith φ ψ -- convolution𝓓Mult (tF2 φ ψ)
--@[simp] def convWith (φ : 𝓓 ℝ Ω ) : 𝓓 ℝ Ω →L[ℝ] 𝓓 ℝ Ω := ContinuousMultilinearMap.toContinuousLinearMap convolution𝓓Mult (tF2 φ 0) 1
notation:67 T " °⋆ " φ => ( convWith  (reflection φ) ) ° T

example  (φ : 𝓓F ℝ V ) (T : 𝓓' ℝ (Full V) ) : ∀ ψ, (T °⋆ φ) ψ = T ( φʳ 𝓓⋆ ψ) := fun _ => rfl
lemma convAsLambda (φ ψ : 𝓓F ℝ V) : (φ 𝓓⋆ ψ) = fun x => Λ φ (shift x (reflection ψ)) := by
  simp
  unfold convolution
  congr


theorem integral_congr {f g : V → ℝ} (p : ∀ x , f x = g x) : ∫ x , f x = ∫ x , g x := by congr ; ext x ; exact p x

-- def smoothFuncForConv (ψ : 𝓓F ℝ V ) :  (𝓓F ℝ V) :=
theorem convolution𝓓'IsSmooth (ψ : 𝓓F ℝ V ) (T : 𝓓'F ℝ V ) : ∃ ψ' , ContDiff ℝ ⊤ ψ'.f ∧ (T °⋆ ψ) = Λ ψ' := by
  let ψ' : LocallyIntegrableFunction V := ⟨ fun x => by
    let ψ'' := shift x (reflection ψ)
    exact T ψ'' , by sorry ⟩

  use ⟨ ψ' , by sorry ⟩
  constructor
  · sorry
  · ext φ

    symm
    trans
    · have : Λ ψ' φ = ∫ x , φ x  * T (shift x (reflection ψ)) := by apply integral_congr ; intro x; rw [mul_comm]
      exact this
    ·
      trans
      · apply integral_congr
        intro x
        symm
        exact T.map_smul (φ.φ x) _

      · let biφ : V → 𝓓F ℝ V := fun x => φ x • (shift x) (reflection ψ)
        have hbiφ : HasCompactSupport (fun x y => biφ y x) := by sorry
        trans  ;
        · symm ; exact FcommWithIntegrals V biφ hbiφ T
        · simp
          congr
          ext y
          trans ; swap
          · exact (congrFun (convAsLambda ( reflection ψ) (φ )) y).symm
          · simp
            --just use linear transformation x = y-v
            sorry


            --change












        -- rw [ (FcommWithIntegrals V ((φ.φ x) • ((shift x) ψ)) T)]









    sorry
