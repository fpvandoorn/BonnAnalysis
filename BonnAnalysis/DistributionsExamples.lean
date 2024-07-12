import Mathlib.Topology.Sequences
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order
import Mathlib.Order.Filter.Basic
import Mathlib.Init.Function
import BonnAnalysis.ConvergingSequences
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Data.Set.Pointwise.Basic
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
open scoped Pointwise
universe u v w
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
  [NormedAddCommGroup V]  [NormedSpace k V]  := 𝓓 k (⊤:Opens V)
abbrev 𝓓'F  (k : Type v) (V : Type u) [NontriviallyNormedField k]
 [NormedAddCommGroup V]  [NormedSpace k V]  := 𝓓' k (Full V)
class GoodEnoughAutom (k : Type v) (V : Type u)[NontriviallyNormedField k]  [MeasurableSpace V] [NormedAddCommGroup V]  [NormedSpace k V] (Φ : V → V) : Prop where
  isLinear : IsLinearMap k Φ
  --IsInjective : Function.Injective Φ
  IsProper : IsProperMap Φ
  isSmooth : ContDiff k ⊤ Φ

  --restToΩ : Φ '' Ω ⊆ Ω
  -- inj : Function.Injective Φ
open GoodEnoughAutom
variable {V : Type u} {k : Type v} [NontriviallyNormedField k]
  [MeasurableSpace V] [NormedAddCommGroup V]  [NormedSpace k V] {Ω : Opens V}
open LinearMap
def toLinearAuto (Φ) [GoodEnoughAutom k V Φ] : (V →L[k] V) := by
  apply ContinuousLinearMap.mk ; swap
  apply IsLinearMap.mk'  (Φ) (isLinear (k :=k) (V:=V))
  sorry










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
lemma tsupport_comp_subset {M N α : Type*} [TopologicalSpace α ] [TopologicalSpace M] [TopologicalSpace N] [Zero M] [Zero N] {g : M → N} (hg : g 0 = 0) (f : α → M) :
    tsupport (g ∘ f) ⊆ tsupport f := by
        apply closure_minimal
        · trans support f
          · apply support_comp_subset ; exact hg
          · exact subset_tsupport f
        · exact isClosed_tsupport f
open Convolution

section CommGroup
lemma sum_compact_subsets {G : Type*} [AddCommGroup G]  [TopologicalSpace G] [TopologicalAddGroup G] {A B : Set G} (hA : IsCompact A) (hB : IsCompact B)
  : IsCompact (A + B ) := by
    let plus : G × G → G := fun p  => p.1 + p.2
    have check : plus '' (A ×ˢ B) = A + B := add_image_prod
    rw [← check]
    apply IsCompact.image
    exact IsCompact.prod hA hB

    exact continuous_add
  -- use that images of compact subsets under + : G x G → G are compact.
lemma tsupport_convolution_subset {𝕜 : Type*}[NontriviallyNormedField 𝕜] {G : Type*} [MeasurableSpace G] (μ : Measure G) {E : Type*} {E' : Type*}  {F : Type*}
  [NormedAddCommGroup F] [NormedAddCommGroup E] [NormedAddCommGroup E']
   [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
  [AddCommGroup G]  [TopologicalSpace G]  [TopologicalAddGroup G]
 (L : E →L[𝕜] E' →L[𝕜] F) {f : G → E} {g : G → E'} (hf : HasCompactSupport f) (hg : HasCompactSupport g) : tsupport (f ⋆[L, μ] g) ⊆ tsupport f + tsupport g:=by
  apply closure_minimal
  · trans support f + support g
    · apply support_convolution_subset
    · have a1 := subset_tsupport (f) ;
      have a2 := subset_tsupport g ;
      exact add_subset_add a1 a2
  · have : IsCompact ( tsupport f + tsupport g) := by
      apply sum_compact_subsets
      exact hf
      exact hg
    sorry


@[simp] def fromAutoOfV (Φ : V → V) [GoodEnoughAutom k V Φ] : 𝓓F k V →L[k] 𝓓F k V := by
  apply mk ; swap
  ·   intro ψ
      use ψ ∘ Φ
      · exact ContDiff.comp ψ.φIsSmooth (isSmooth)
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
        -- apply TendstoUniformly.comp
        have th : ∀ {n  : ℕ∞} , n ≤ ⊤ := OrderTop.le_top _
        have q := fun l =>  (φ l).φIsSmooth
        let myΦ : (i : Fin l) → V →L[k] V :=  fun _ ↦ toLinearAuto Φ
        let precompmyΦ: (V [×l]→L[k] k) → (V [×l]→L[k] k) := fun θ ↦ θ.compContinuousLinearMap (myΦ)


        have chainRule {φ0 : 𝓓F k V} : (iteratedFDeriv k l (φ0 ∘ Φ)) =
          (precompmyΦ ∘ (iteratedFDeriv k l (φ0).φ ∘ Φ )) := by
          ext1 x
          exact ContinuousLinearMap.iteratedFDeriv_comp_right (toLinearAuto Φ) ((φ0).φIsSmooth) x th
        have : (fun n => iteratedFDeriv k l ((φ n).φ ∘ Φ) ) = (fun n => precompmyΦ ∘ iteratedFDeriv k l (φ n).φ ∘ Φ )  := by
           ext1 n
           exact chainRule
        have hφ' : TendstoUniformly (fun n => (iteratedFDeriv k l (φ n).φ ∘ Φ)) ((iteratedFDeriv k l φ0.φ) ∘ Φ) atTop
          :=  TendstoUniformly.comp (hφ l) (Φ)
        have : TendstoUniformly (fun n => iteratedFDeriv k l (φ n ∘ Φ) ) (iteratedFDeriv k l (φ0 ∘ Φ)) atTop := by
          rw [chainRule (φ0 := φ0)]
          rw [this]
          apply UniformContinuous.comp_tendstoUniformly (g:= precompmyΦ)
          · sorry -- apply UniformFun.postcomp_uniformContinuous , uniform Inducing?
          · apply TendstoUniformly.comp
            exact hφ l

        exact this



        -- rw [this]

        -- rw [] --
        -- exact hφ l




@[simp] def reflection' : V → V := fun x => -x
@[simp] def shift' (x : V) : V → V := fun y => y - x

instance : (GoodEnoughAutom k V) reflection' where
  isLinear := by sorry
  isSmooth := by sorry
  IsProper := by sorry
  --restToΩ := by sorry
--  inj := by sorry

instance (v : V) :  (GoodEnoughAutom k V) (shift' v) where
  isLinear := by sorry
  isSmooth := by sorry
  IsProper := by sorry
  --restToΩ := by sorry
 -- inj := by sorry


/--
    SOLVED    Issue: If φ ψ : V → k and are smooth on Ω , how to show that the derivative is additive outside Ω ?
        --/
lemma zeroCase {φ : ℕ → (V → k)} {φ0 : V → k} :
  (TendstoUniformly (fun n ↦ iteratedFDeriv k 0 (φ n)) (iteratedFDeriv k 0 φ0) atTop) ↔
    TendstoUniformly (fun n => (φ n) ) (φ0) atTop := by

        rw [iteratedFDeriv_zero_eq_comp]
        have myrw : (fun n ↦ iteratedFDeriv k 0 (φ n)) = fun n ↦ (⇑(continuousMultilinearCurryFin0 k V k).symm ∘ (φ n)) := by
          ext1 n
          rw [iteratedFDeriv_zero_eq_comp]
        rw [myrw]
        constructor
        · apply UniformContinuous.comp_tendstoUniformly (g:=⇑(continuousMultilinearCurryFin0 k V k)) ?_
          apply Isometry.uniformContinuous
          apply LinearIsometryEquiv.isometry
        · apply UniformContinuous.comp_tendstoUniformly (g:=⇑(continuousMultilinearCurryFin0 k V k).symm) ?_
          apply Isometry.uniformContinuous
          apply LinearIsometryEquiv.isometry
def δ : 𝓓' k Ω := mk k (fun φ => φ 0) (by
  constructor
  · intro x y ; rfl
  · intro c x ; rfl
  · constructor
    intro x a hx
    apply TendstoUniformly.tendsto_at
    have := hx.2 0
    apply zeroCase.mp
    assumption
    )
lemma testfunctionIsDiffAt {φ : 𝓓 k Ω} (x : V) : DifferentiableAt k (φ) x := by
  apply ContDiffAt.differentiableAt
  · apply contDiff_iff_contDiffAt.mp
    exact φ.φIsSmooth
  · exact OrderTop.le_top 1
def fderiv𝓓 (v : V) : (𝓓 k Ω) →L[k] 𝓓 k Ω := by
  let f : 𝓓 k Ω → 𝓓 k Ω := fun φ => ⟨ fun x => fderiv k φ x v , by sorry , by sorry , by sorry ⟩
  apply mk ; swap
  · exact f
  · constructor
    ·     intro φ ψ
          ext x
          by_cases p : x ∈ Ω ; swap
          · trans (fderiv k φ x + fderiv k ψ x) v
            · apply congrFun (congrArg DFunLike.coe ?_) v ; apply fderiv_add ; apply testfunctionIsDiffAt ;apply testfunctionIsDiffAt ;
            · rfl

          · have : (fderiv k (fun y => φ.φ y + ψ.φ y) x) = (fderiv k φ.φ x) + (fderiv k ψ.φ x) := by
              apply fderiv_add
              · exact diffAt k Ω φ p
              · exact diffAt k Ω ψ p
            have obv : ((fderiv k (fun y => φ.φ y + ψ.φ y) x)) v = (fderiv k φ.φ x) v + (fderiv k ψ.φ x) v := by
              rw [this]
              rfl
            exact obv
    · intro c φ
      ext x
      simp
      trans (c • (fderiv k φ.φ x)) v
      · apply congrFun (congrArg DFunLike.coe ?_) v
        apply fderiv_const_smul (E:=V) (f:= φ.φ) (𝕜 := k) (R:=k) (F:=k) (x:=x) ?_ c
        apply testfunctionIsDiffAt
      · rfl
    · constructor
      intro α  a hx
      apply tendsTo𝓝
      constructor
      · obtain ⟨ K , hK ⟩ := hx.1
        use K
        constructor
        · exact hK.1
        · intro n
          trans (tsupport (α n).φ)
          · trans ; swap
            · exact tsupport_fderiv_subset k (f:= (α n).φ)
            · have : ((f ∘ α) n).φ = (fun q => q v) ∘ fderiv k (α n).φ := rfl
              rw [this]
              apply tsupport_comp_subset  (rfl) (fderiv k (α n).φ)


          · exact hK.2 n
      · intro l
        have : TendstoUniformly (fun n ↦ iteratedFDeriv k (l+1) (α  n).φ) (iteratedFDeriv k (l+1) (a).φ) atTop := hx.2 (l+1)
        let g : (V[×(l+1)]→L[k] k) → (V[×l]→L[k] k)  := fun φ => (ContinuousMultilinearMap.curryLeft φ) v-- evaluation at v
        have hxg (ψ : 𝓓 k Ω)  :  iteratedFDeriv k l (f ψ).φ = g ∘ iteratedFDeriv k (l + 1) (ψ).φ := by
          calc
           _ = iteratedFDeriv k l (fun y => fderiv k ψ.φ y v) := rfl

           -- _ = fun z => iteratedFDeriv k (l + 1) ψ.φ ) := by sorry
           _ = fun z => (ContinuousMultilinearMap.curryLeft (iteratedFDeriv k (l + 1) ψ.φ z) v) := by ext1 z ; sorry
           _ = g ∘ iteratedFDeriv k (l + 1) (ψ).φ := rfl

             -- rw [← iteratedFDeriv_succ_eq_comp_left]

        rw [hxg]
        have hxg :  (fun (n : ℕ) => iteratedFDeriv k l ((f ∘ α ) n).φ) =
          fun (n : ℕ) => g ∘ (iteratedFDeriv k (l + 1) (α  n).φ) := by
            ext1 n
            exact hxg (α n)


        rw [hxg]

        rw [← tendstoUniformlyOn_univ ] at this
        rw [← tendstoUniformlyOn_univ ]
        apply UniformContPresUniformConvergence this g
        sorry




example (v : V) (φ : 𝓓 k Ω ) (T : 𝓓' k Ω ): (fderiv𝓓 v ° T) φ = T (fderiv𝓓 v φ) := by rfl
-- def reflection : 𝓓 k Ω → 𝓓 k Ω := fun ψ => ⟨ fun x => ψ (-x) , by sorry , by sorry ⟩
-- instance : AddHomClass reflection _ _ where



@[simp] def reflection  : 𝓓F k V →L[k] (𝓓F k V) := fromAutoOfV reflection'


notation:67 ψ "ʳ" => reflection ψ

---------- the rest deals with real numbers
variable  (V : Type u) [MeasureSpace V] [NormedAddCommGroup V]  [NormedSpace ℝ V]
  [MeasureSpace V] [OpensMeasurableSpace V] {Ω : Opens V} [OpensMeasurableSpace V]  [IsFiniteMeasureOnCompacts (volume (α := V))] --[IsFiniteMeasureOnCompacts (volume V)]

structure LocallyIntegrableFunction where
   f : V → ℝ
   hf : MeasureTheory.LocallyIntegrable f


def intSm (φ : V → 𝓓F ℝ V)  (hφ : HasCompactSupport (fun x y => φ y x)) : 𝓓F ℝ V := ⟨ fun y => ∫ x , φ y x , by sorry , by sorry , by sorry⟩
-- ContinuousLinearMap.integral_comp_comm PROBLEM: 𝓓F ℝ V is not NormedAddGroup so we cant apply
-- probably some smoothness condition on φ is missing anyway really Ccinfty(Ω × Ω ) needed?
lemma FcommWithIntegrals (φ : V → 𝓓F ℝ V)  (hφ : HasCompactSupport (fun x y => φ y x)) (T : 𝓓'F ℝ V) : T (intSm V φ hφ) =  ∫ x : V ,  T (φ x)  := by
  symm

  -- have : Integrable φ := by sorry
  -- rw [ContinuousLinearMap.integral_comp_comm T.1]



  sorry
--def fromCurrying (φ : V → 𝓓F ℝ V)  (hφ : HasCompactSupport (fun x y => φ y x)) : 𝓓F ℝ (V × V ) := ⟨ fun x => φ x.1 x.2 , by sorry  , by sorry ,   fun ⦃a⦄ a ↦ trivial ⟩ -- todo
lemma testFunctionIsLocallyIntegrable
  (φ : 𝓓 ℝ Ω  ) : MeasureTheory.LocallyIntegrable φ := by
    apply MeasureTheory.Integrable.locallyIntegrable
    apply Continuous.integrable_of_hasCompactSupport
    exact ContDiff.continuous (𝕜:=ℝ) φ.φIsSmooth
    exact φ.φHasCmpctSupport




variable {V : Type u}  [MeasureSpace V]
   [NormedAddCommGroup V]  [NormedSpace ℝ V] [BorelSpace V] {Ω : Opens V} [OpensMeasurableSpace V]  [IsFiniteMeasureOnCompacts (volume (α := V))]

instance : Coe ( 𝓓F ℝ V) (LocallyIntegrableFunction V) where
  coe φ := ⟨ φ , testFunctionIsLocallyIntegrable V φ ⟩

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
lemma  ConvWithIsUniformContinuous-- [BorelSpace V]
   {k' : Type w}  [MeasureSpace k'] [NormedAddCommGroup k']  [NormedSpace ℝ k']
   {φ : 𝓓F ℝ V} {ψ : ℕ → V → k'} {ψ0 : V → k'} (hψ : TendstoUniformly ψ ψ0 atTop)
    {L : ℝ  →L[ℝ ] k' →L[ℝ] ℝ} :
    TendstoUniformly (β := ℝ) (fun n => (φ.φ ⋆[L] (ψ n))) ((φ.φ ⋆[L] ψ0)) atTop := by sorry -- help exact UniformContinuous.comp_tendstoUniformly (g:= fun ψ => φ.φ ⋆ ψ) ?_ ?_
         /-
             I want to use somehow that (φ ⋆ _) is uniformly continuous (what is domain / codomain) to deduce that
              it preserve Uniform sequences.
            exact UniformContinuous.comp_tendstoUniformly (g:= fun ψ => φ.φ ⋆ ψ) ?_ this
            -/
lemma  iteratedDerivConv {V : Type u}  [MeasureSpace V]
   [NormedAddCommGroup V]  [NormedSpace ℝ V] [BorelSpace V]
  {k' : Type w}  [MeasureSpace k'] [NormedAddCommGroup k']  [NormedSpace ℝ k']
    {φ : 𝓓F ℝ V}  {ψ : ℕ → V → k'} {ψ0 : V → k'} (hψ : TendstoUniformly ψ ψ0 atTop) {l : ℕ}
    {L : ℝ  →L[ℝ ] k' →L[ℝ] ℝ} :
    TendstoUniformly (fun n => iteratedFDeriv ℝ (l+1) (φ.φ ⋆[L] (ψ n))) (iteratedFDeriv ℝ (l+1) (φ.φ ⋆[L] ψ0)) atTop := by sorry
lemma convOfTestFunctionsExists [T2Space V] {φ ψ : 𝓓F ℝ V} : ConvolutionExists φ.φ ψ.φ (ContinuousLinearMap.lsmul ℝ ℝ) := by
  intro x ;
  apply HasCompactSupport.convolutionExists_right -- HasCompactSupport.convolutionExistsAt
  exact  ψ.φHasCmpctSupport --HasCompactSupport.convolution φ.φHasCmpctSupport
  exact testFunctionIsLocallyIntegrable V φ
  apply ContDiff.continuous (𝕜:=ℝ ) (ψ.φIsSmooth)


@[simp] def convWith  ( φ : 𝓓F ℝ V) : (𝓓F ℝ V) →L[ℝ] 𝓓F ℝ V := by
  apply mk ℝ  ; swap
  intro ψ
  use  φ ⋆ ψ
  --rw [← contDiffOn_univ] ;
  · apply HasCompactSupport.contDiff_convolution_right
    · exact ψ.φHasCmpctSupport
    · exact (testFunctionIsLocallyIntegrable V φ)
    · exact ψ.φIsSmooth
  · apply HasCompactSupport.convolution
    · exact φ.φHasCmpctSupport
    · exact ψ.φHasCmpctSupport
  · exact fun ⦃a⦄ a ↦ trivial
  · constructor
    · intro ψ₁ ψ₂ ; ext z ; simp ; apply ConvolutionExistsAt.distrib_add ; exact convOfTestFunctionsExists z ; exact convOfTestFunctionsExists z --help
    · intro c ψ ; ext z ; simp ; exact congrFun (convolution_smul (𝕜 := ℝ ) (F:= ℝ ) (G:= V) (f:=φ.φ) (g:= ψ.φ) ) z
    · constructor
      intro ψ ψ0 hψ
      apply tendsTo𝓝
      constructor
      · obtain ⟨ K , hK⟩ := hψ.1
        use tsupport (φ) + K
        constructor
        · apply sum_compact_subsets
          exact φ.φHasCmpctSupport
          exact hK.1
        -- · apply IsCompact.union
        --   exact φ.φHasCmpctSupport
        --   exact hK.1
        · intro n
          have : tsupport (φ.φ ⋆ (ψ n).φ) ⊆ tsupport φ.φ + tsupport (ψ n).φ := by
            apply tsupport_convolution_subset
          trans
          · exact this
          · apply add_subset_add_left
            exact hK.2 n



      · intro l
        induction' l with l hl -- ψ ψ0 hψ --
        · simp
          apply (zeroCase (φ := fun n => φ ⋆ ψ n)).mpr
          exact ConvWithIsUniformContinuous (zeroCase.mp (hψ.2 0))
        · apply iteratedDerivConv
          exact (zeroCase.mp (hψ.2 0))


notation:67 φ " 𝓓⋆ " ψ => convWith φ ψ -- convolution𝓓Mult (tF2 φ ψ)
--@[simp] def convWith (φ : 𝓓 ℝ Ω ) : 𝓓 ℝ Ω →L[ℝ] 𝓓 ℝ Ω := ContinuousMultilinearMap.toContinuousLinearMap convolution𝓓Mult (tF2 φ 0) 1
notation:67 T " °⋆ " φ => ( convWith  (reflection φ) ) ° T

example  (φ : 𝓓F ℝ V ) (T : 𝓓' ℝ (Full V) ) : ∀ ψ, (T °⋆ φ) ψ = T ( φʳ 𝓓⋆ ψ) := fun _ => rfl
lemma convAsLambda (φ ψ : 𝓓F ℝ V) : (φ 𝓓⋆ ψ) = fun x => Λ (φ ) (shift x (reflection ψ)) := by
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
            --just use linear transformation x = y-v --help
            sorry


            --change












        -- rw [ (FcommWithIntegrals V ((φ.φ x) • ((shift x) ψ)) T)]
-- #lint
