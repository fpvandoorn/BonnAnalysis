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
open ContinuousLinearEquiv
variable {V : Type u} {k : Type v} [NontriviallyNormedField k]
  [MeasurableSpace V] [NormedAddCommGroup V]  [NormedSpace k V] {Ω : Opens V}
variable  (W : Type* )  [NormedAddCommGroup W]  [NormedSpace k W]

def ev_cts  (v : V) {W : Type* }  [NormedAddCommGroup W]  [NormedSpace k W]  :
  (V →L[k] W) →L[k] W := ContinuousLinearMap.apply _ _ v


open LinearMap
def toLinearAuto (Φ) [GoodEnoughAutom k V Φ] : (V →L[k] V) := by
  apply ContinuousLinearMap.mk ; swap
  apply IsLinearMap.mk'  (Φ) (isLinear (k :=k) (V:=V))
  have : Continuous Φ  := by sorry
  assumption



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
  [AddCommGroup G]  [TopologicalSpace G]  [TopologicalAddGroup G]  [T2Space G]
 (L : E →L[𝕜] E' →L[𝕜] F) {f : G → E} {g : G → E'} (hf : HasCompactSupport f) (hg : HasCompactSupport g) : tsupport (f ⋆[L, μ] g) ⊆ tsupport f + tsupport g:=by
  apply closure_minimal
  · trans support f + support g
    · apply support_convolution_subset
    · have a1 := subset_tsupport (f)
      have a2 := subset_tsupport g
      exact add_subset_add a1 a2
  · have : IsCompact ( tsupport f + tsupport g) := by
      apply sum_compact_subsets
      exact hf
      exact hg
    -- maybe use that compact subsets of metrizable spaces are closed?
    exact IsCompact.isClosed this


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
      · exact fun _ _ ↦ trivial
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
        let myΦ : (i : Fin l) → V →L[k] V :=  fun _ ↦ toLinearAuto Φ
        let precompmyΦ: (V [×l]→L[k] k) →L[k] (V [×l]→L[k] k) := ContinuousMultilinearMap.compContinuousLinearMapL (myΦ)


        have chainRule {φ0 : 𝓓F k V} : (iteratedFDeriv k l (φ0 ∘ Φ)) =
          (precompmyΦ ∘ (iteratedFDeriv k l (φ0).φ ∘ Φ )) := by
          ext1 x
          exact ContinuousLinearMap.iteratedFDeriv_comp_right (toLinearAuto Φ) ((φ0).φIsSmooth) x th
        have : (fun n => iteratedFDeriv k l ((φ n).φ ∘ Φ) ) = (fun n => precompmyΦ ∘ iteratedFDeriv k l (φ n).φ ∘ Φ )  := by
           ext1 n
           exact chainRule
        have : TendstoUniformly (fun n => iteratedFDeriv k l (φ n ∘ Φ) ) (iteratedFDeriv k l (φ0 ∘ Φ)) atTop := by
          rw [chainRule (φ0 := φ0)]
          rw [this]
          apply UniformContinuous.comp_tendstoUniformly (g:= precompmyΦ)
          · apply ContinuousLinearMap.uniformContinuous -- apply UniformFun.postcomp_uniformContinuous , uniform Inducing?
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

def δ : 𝓓' k Ω := mk k (fun φ => φ 0) (by
  constructor
  · intro x y ; rfl
  · intro c x ; rfl
  · constructor
    intro x a hx
    apply TendstoUniformly.tendsto_at
    have := hx.2 0
    apply (zeroCase k).mp
    assumption
    )
lemma testfunctionIsDiffAt {φ : 𝓓 k Ω} (x : V) : DifferentiableAt k (φ) x := by
  apply ContDiffAt.differentiableAt
  · apply contDiff_iff_contDiffAt.mp
    exact φ.φIsSmooth
  · exact OrderTop.le_top 1
def fderiv𝓓 (v : V) : (𝓓 k Ω) →L[k] 𝓓 k Ω := by
  have obs {φ : V → k} : tsupport (fun x => fderiv k φ x v) ⊆ tsupport (φ) := by -- ⊆ tsupport (fun x => fderiv k φ) :=
    trans ; swap
    · exact tsupport_fderiv_subset k (f:= φ)
    · apply tsupport_comp_subset rfl (g := fun f => f v)  (f:=fderiv k φ)
  let f : 𝓓 k Ω → 𝓓 k Ω := fun φ => by
    use fun x => fderiv k φ x v
    · have dfh : ContDiff k ⊤ (fun x => fderiv k φ.φ x) := (contDiff_top_iff_fderiv.mp (φ.φIsSmooth )).2

      have evvh : ContDiff k ⊤ (NormedSpace.inclusionInDoubleDual k V v) := by apply ContinuousLinearMap.contDiff

      apply ContDiff.comp  evvh dfh


    · apply IsCompact.of_isClosed_subset (φ.φHasCmpctSupport)
      exact isClosed_tsupport fun x ↦ (fderiv k φ.φ x) v
      exact obs
    ·
          trans
          · exact obs
          · exact φ.sprtinΩ
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
          · exact obs
          · exact hK.2 n
      · intro l
        have : TendstoUniformly (fun n ↦ iteratedFDeriv k (l+1) (α  n).φ) (iteratedFDeriv k (l+1) (a).φ) atTop := hx.2 (l+1)
        let g1 : (V[×(l+1)]→L[k] k) ≃ₗᵢ[k] V →L[k] (V[×l]→L[k] k) := (continuousMultilinearCurryLeftEquiv k (fun _ => V) k).symm
        let g1 : (V[×(l+1)]→L[k] k) →L[k] V →L[k] (V[×l]→L[k] k)  := ContinuousLinearEquiv.toContinuousLinearMap g1
        let g : (V[×(l+1)]→L[k] k) →L[k] (V[×l]→L[k] k)  :=  ( ev_cts v).comp g1 --todo replace by ev_cts
    --     have step (f : V → k ) (z : V) : iteratedFDeriv k l (fderiv k f) z =
    -- ContinuousMultilinearMap.curryLeft (iteratedFDeriv k (l + 1) f z) := congrFun (fderiv_iteratedFDeriv (𝕜 := k) (f:= f)) z
        have hxg (ψ : 𝓓 k Ω)  :  iteratedFDeriv k l (f ψ).φ = g ∘ iteratedFDeriv k (l + 1) (ψ).φ := by
          calc
           _ = iteratedFDeriv k l (fun y => fderiv k ψ.φ y v) := rfl
           _ = fun z => (ContinuousMultilinearMap.curryLeft (iteratedFDeriv k (l + 1) ψ.φ z) v) := by ext1 z ; sorry --exact?
           _ = g ∘ iteratedFDeriv k (l + 1) (ψ).φ := by rfl -- ext1 z ; simp
        rw [hxg]
        have hxg :  (fun (n : ℕ) => iteratedFDeriv k l ((f ∘ α ) n).φ) =
          fun (n : ℕ) => g ∘ (iteratedFDeriv k (l + 1) (α  n).φ) := by
            ext1 n
            exact hxg (α n)


        rw [hxg]

        rw [← tendstoUniformlyOn_univ ] at this
        rw [← tendstoUniformlyOn_univ ]
        apply UniformContPresUniformConvergence this g
        apply ContinuousLinearMap.uniformContinuous




example (v : V) (φ : 𝓓 k Ω ) (T : 𝓓' k Ω ): (fderiv𝓓 v ° T) φ = T (fderiv𝓓 v φ) := by rfl



@[simp] def reflection  : 𝓓F k V →L[k] (𝓓F k V) := fromAutoOfV reflection'


notation:67 ψ "ʳ" => reflection ψ

---------- the rest deals with real numbers
variable  (V : Type u) [MeasureSpace V] [NormedAddCommGroup V]  [NormedSpace ℝ V]
  [MeasureSpace V] [OpensMeasurableSpace V] {Ω : Opens V} [OpensMeasurableSpace V]  [IsFiniteMeasureOnCompacts (volume (α := V))] --[IsFiniteMeasureOnCompacts (volume V)]

structure LocallyIntegrableFunction where
   f : V → ℝ
   hf : MeasureTheory.LocallyIntegrable f


@[simp] def intSm (φ : V → 𝓓F ℝ V)  (hφ : HasCompactSupport (fun x y => φ y x)) : 𝓓F ℝ V := ⟨ fun y => ∫ x , φ y x , by sorry , by sorry , by sorry⟩
-- ContinuousLinearMap.integral_comp_comm PROBLEM: 𝓓F ℝ V is not NormedAddGroup so we cant apply
-- probably some smoothness condition on φ is missing anyway really Ccinfty(Ω × Ω ) needed?
lemma FcommWithIntegrals (φ : V → 𝓓F ℝ V)  (hφ : HasCompactSupport (fun x y => φ y x)) (T : 𝓓'F ℝ V) : T (intSm V φ hφ) =  ∫ x : V ,  T (φ x)  := by
  symm
  sorry

  -- have : Integrable φ := by sorry
  -- rw [ContinuousLinearMap.integral_comp_comm T.1]

lemma testFunctionIsLocallyIntegrable
  (φ : 𝓓 ℝ Ω  ) : MeasureTheory.LocallyIntegrable φ := by
    apply MeasureTheory.Integrable.locallyIntegrable
    apply Continuous.integrable_of_hasCompactSupport
    exact ContDiff.continuous (𝕜:=ℝ) φ.φIsSmooth
    exact φ.φHasCmpctSupport




variable {V : Type u}  [MeasureSpace V]
   [NormedAddCommGroup V]  [NormedSpace ℝ V] [MeasureTheory.Measure.IsAddHaarMeasure (volume : Measure V)] [BorelSpace V] {Ω : Opens V}

instance : Coe ( 𝓓F ℝ V) (LocallyIntegrableFunction V) where
  coe φ := ⟨ φ , testFunctionIsLocallyIntegrable V φ ⟩


--lemma FcommWithIntegrals [MeasureSpace Ω] (φ : 𝓓 ℝ (squareOpen Ω )) (T : 𝓓' ℝ Ω) :  ∫ x , T (𝓓kSquareCurry φ x) = T (intSm φ) := by sorry
--def transport (φ : 𝓓 k Ω) {ψ : V → ℝ} (p : φ = ψ) : 𝓓 k Ω
notation "|| " f " ||_∞" => MeasureTheory.snormEssSup f volume
instance  :  CoeFun (LocallyIntegrableFunction V) (fun _ => V → ℝ) where
  coe σ := σ.f
open MeasureSpace


--
     -- let b' :  ℝ≥0 :=  --



/-
MeasureTheory.lintegral_indicator
theorem MeasureTheory.lintegral_indicator {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} (f : α → ENNReal) {s : Set α} (hs : MeasurableSet s) :
∫⁻ (a : α), Set.indicator s f a ∂μ = ∫⁻ (a : α) in s, f a ∂μ
-/

      --sorry
--​integral_eq_integral_of_support_subset
lemma TendstoUniformly_iff_uniformZeroSeq {φ  : ℕ → V → k} {φ₀ : V → k} : TendstoUniformly φ φ₀ atTop ↔ TendstoUniformly (fun n => φ n - φ₀) 0 atTop := by
          constructor
          · intro hφ
            rw [show (0 = φ₀ - φ₀) from (by simp)]
            apply TendstoUniformly.sub hφ
            rw [← tendstoUniformlyOn_univ]
            apply CnstSeqTendstoUniformlyOn
          · sorry
lemma shouldExist  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : E' → E)  [MeasureSpace E'] (K : Set E') (hK : support f ⊆ K)
  : ∫ (x : E' ) , f x = ∫ (x : E') in K , f x := by sorry
@[simp] def Λ (f : LocallyIntegrableFunction V) : 𝓓' ℝ Ω := by
  apply mk ; swap
  · exact fun φ => ∫ v , f v * φ v
  · constructor
    · intro x y ; sorry -- rw [Integral.distrib_add] ; sorry
    · sorry
    · constructor
      intro φ φ₀  hφ
      obtain ⟨ K , hK ⟩ := hφ.1

      rw [← tendsto_sub_nhds_zero_iff]
      simp_rw [ NormedAddCommGroup.tendsto_nhds_zero, eventually_atTop ]

      have : ∀ (f : V → ℝ) x , ‖ f x ‖₊ ≤ || f ||_∞ := by sorry
      have {a b : ℝ } : ENNReal.ofReal (‖ a‖ * ‖b‖) = ↑(‖a‖₊ * ‖b‖₊) := by
        calc
           ENNReal.ofReal (‖ a‖ * ‖b‖) = ENNReal.ofReal (‖ a * b‖) := by congr ; rw [← norm_mul]
           _ = ↑(‖ a * b‖₊)  := by exact ofReal_norm_eq_coe_nnnorm (a * b)
           _ = ↑(‖a‖₊ * ‖b‖₊) := by congr ; exact nnnorm_mul a b
        -- rw [← show ENNReal.ofNNReal ⟨ ‖a‖₊ * ‖b‖₊ , ?_ ⟩ = ↑(‖a‖₊ * ‖b‖₊) from ?_] -- symm ; rw [ENNReal.coe_mul ‖a‖₊ ‖b‖₊] ;
        -- sorry
        -- apply?


--(ha :  a ≠ ⊤ ) (hb : b ≠ ⊤ )
      have mainArg : ∀ n ,
         ‖  (∫ (v : V), f.f v * (φ n).φ v)  - ∫ (v : V), f.f v * φ₀.φ v ‖₊
        ≤  ENNReal.toReal (∫⁻ (v : V) in K,   ‖ (f v) ‖₊ ) * ENNReal.toReal (|| (φ n).φ - φ₀.φ ||_∞) := by
        intro n
        have fIsIntegrableOnK := LocallyIntegrable.integrableOn_isCompact f.hf hK.1
        have integrable {ψ : V → ℝ} (hψ : tsupport ψ ⊆ K): Integrable (fun v ↦ f.f v * ψ v) volume := by
          have hf : ((fun v ↦ f.f v * ψ v) = fun v => ψ v * K.indicator f.f v ) := by sorry
          rw [hf]
          apply MeasureTheory.Integrable.bdd_mul
          · sorry
          · sorry
          have : ∃ C, ∀ (x : V), ‖ψ x‖ ≤ C := by sorry
          exact this



        have supportφ₀ := KcontainsSuppOfLimit ℝ Ω hφ hK
        have someArg : (support fun x => f.f x * ((φ n).φ - φ₀.φ) x) ⊆ K := by
          rw [Function.support_mul (f.f) (φ n - φ₀)]
          trans
          · exact inter_subset_right
          rw [← Set.union_self K]
          trans
          · apply Function.support_sub
          · apply Set.union_subset_union
            · trans ; exact subset_tsupport _ ; exact hK.2 n
            · trans ; exact subset_tsupport _ ; exact supportφ₀
        have someOtherArg : (∫⁻ (v : V) in K , ‖ f.f v ‖₊ * ‖ ((φ n).φ -φ₀.φ) v ‖₊ ).toReal  ≤
          (∫⁻ (v : V) in K , ‖ f.f v ‖₊ * || ((φ n).φ -φ₀.φ) ||_∞ ).toReal := by
          have : || (φ n).φ - φ₀.φ ||_∞ ≠ ⊤ := by sorry
          apply ENNReal.toReal_mono ;
          · sorry ;
          · apply MeasureTheory.lintegral_mono_ae ;
            --rw
            have {a : V}  (ha : ‖ ((φ n).φ -φ₀.φ) a‖₊   ≤   || ((φ n).φ -φ₀.φ) ||_∞ ) :
              ↑‖f.f a‖₊ * ↑‖((φ n).φ - φ₀.φ) a‖₊ ≤ ↑‖f.f a‖₊ * || (φ n).φ - φ₀.φ ||_∞ := by
              calc
              _ = ENNReal.ofNNReal (‖f.f a‖₊ * ‖((φ n).φ - φ₀.φ) a‖₊) := by rfl
              _ ≤ ENNReal.ofNNReal (‖f.f a‖₊ * || ((φ n).φ -φ₀.φ) ||_∞.toNNReal) := by apply ENNReal.coe_mono ; apply mul_le_mul_left'  ; refine ENNReal.toNNReal_mono ?_ ha ; exact this
              _ = ENNReal.ofNNReal (‖f.f a‖₊) * (ENNReal.ofNNReal  || ((φ n).φ -φ₀.φ) ||_∞.toNNReal) := by apply ENNReal.coe_mul
              _ = _ := by congr; apply ENNReal.coe_toNNReal ; exact this
            rw [Filter.eventually_iff]
            apply sets_of_superset
            · apply MeasureTheory.ae_le_snormEssSup (f:=((φ n).φ -φ₀.φ))
            · intro x hx
              apply this
              trans
              · exact hx
              · apply MeasureTheory.snormEssSup_mono_measure
                sorry

        have fIsMeasureable : Measurable fun a ↦ ENNReal.ofNNReal ‖f.f a‖₊ := by sorry
        calc
        ‖  (∫ (v : V), f.f v * (φ n).φ v)  - ∫ (v : V), f.f v * φ₀.φ v‖
          = ‖  ∫ (v : V) , f.f v * (φ n).φ v - f.f v * φ₀.φ v‖  := by congr ; rw [← MeasureTheory.integral_sub] ; exact integrable (hK.2 n) ; exact integrable supportφ₀
        _ = ‖  ∫ (v : V) , f.f v * ((φ n).φ v -φ₀.φ v)‖ := by congr ; ext1 v ; symm ; exact (smul_sub (f.f v) ((φ n).φ v) (φ₀.φ v))
        _ = ‖  ∫ (v : V) in K , (f.f  * ((φ n).φ -φ₀.φ)) v‖ := by apply congrArg ; apply shouldExist (fun v => f.f v * ((φ n).φ -φ₀.φ) v ) K ; exact someArg
        _ ≤ (∫⁻ (v : V) in K , ENNReal.ofReal ‖ (f.f v * ((φ n).φ -φ₀.φ) v)‖ ).toReal   := by apply MeasureTheory.norm_integral_le_lintegral_norm (f.f * ((φ n).φ -φ₀.φ))
        _ = (∫⁻ (v : V) in K , ‖ f.f v ‖₊ * ‖ ((φ n).φ -φ₀.φ) v ‖₊ ).toReal   := by  congr ; ext v ; simp_rw [norm_mul] ; trans ; swap ;  apply ENNReal.coe_mul ; exact this
        _ ≤ (∫⁻ (v : V) in K , ‖ f.f v ‖₊ * || ((φ n).φ -φ₀.φ) ||_∞ ).toReal   := by exact someOtherArg
        _ = (∫⁻ (v : V) in K , || ((φ n).φ -φ₀.φ) ||_∞  * ‖ f.f v ‖₊ ).toReal   := by congr ; simp_rw [mul_comm]
        _ =  ((|| ((φ n).φ -φ₀.φ) ||_∞) * (∫⁻ (v : V) in K , ‖ f.f v ‖₊ )).toReal := by congr ;  apply MeasureTheory.lintegral_const_mul  (|| ((φ n).φ -φ₀.φ) ||_∞) ; exact fIsMeasureable
        _ = (∫⁻ (v : V) in K , ‖ f.f v ‖₊ ).toReal *  (|| ((φ n).φ -φ₀.φ) ||_∞).toReal   := by rw [ENNReal.toReal_mul , mul_comm]
      have foo {ε} {ψ : V → ℝ} (hε : ε ≥ 0) (p : ∀ x ∈ univ , ‖ ψ x‖  < ε) : || ψ ||_∞.toReal ≤ ε   := by
        have : || ψ ||_∞ ≤ ENNReal.ofReal ε := by
          apply MeasureTheory.snormEssSup_le_of_ae_bound (C:=ε)
          apply ae_of_all volume
          intro a
          apply le_of_lt
          exact p a trivial
        refine ENNReal.toReal_le_of_le_ofReal hε  this
      have hφ : ∀ ε > 0 , ∃ a, ∀ n ≥ a, || (φ n).φ - φ₀.φ ||_∞.toReal < ε := by
        have : ∀ ε > 0 , ∃ a, ∀ n ≥ a,  ∀ x ∈ univ , ‖((φ n).φ - φ₀.φ) x‖ < ε := by
          simp_rw [← eventually_atTop  ]

          have : TendstoUniformly (fun n => (φ n).φ ) φ₀.φ atTop := by apply (zeroCase _).mp ; exact hφ.2 0
          have : TendstoUniformly (fun n => (φ n).φ - φ₀.φ) 0 atTop := by apply TendstoUniformly_iff_uniformZeroSeq.mp this

          apply SeminormedAddGroup.tendstoUniformlyOn_zero.mp (tendstoUniformlyOn_univ.mpr this)
        intro ε hε
        obtain ⟨ a , ha ⟩ := this (ε / 2) (half_pos hε ) -- hε
        use a
        intro n hn
        apply LE.le.trans_lt
        · exact foo (ε := ε / 2) (ψ := (φ n).φ - φ₀.φ) (le_of_lt (half_pos hε)) (ha n hn)
        · exact div_two_lt_of_pos hε
        --

      intro ε hε
      let C : ℝ≥0 := ENNReal.toNNReal (∫⁻ (v : V) in K,   ‖ (f v) ‖₊ )
      by_cases h : C = 0
      · use 0 ; intro b hb ;
        apply LE.le.trans_lt
        · exact mainArg b
        · have : C * (|| (φ b).φ - φ₀.φ ||_∞.toReal) < ε := by
            rw [h] ;
            simp
            exact hε
          exact this
      · let ε' : ℝ := ε / C
        -- have hε' : ε' > 0 ∧
        have hC : 0 < C := pos_iff_ne_zero.mpr h
        obtain ⟨ a , ha ⟩ :=  hφ ε' (by apply (div_pos_iff_of_pos_right ?_).mpr ; exact hε ;   exact hC  )
        use a

        intro b hb
        specialize ha b hb
        apply LE.le.trans_lt
        · exact mainArg b
        · rw [show (ε = C * ε') from ?_]
          · apply (mul_lt_mul_left ?_ ).mpr
            exact ha
            exact hC
          · refine Eq.symm (IsUnit.mul_div_cancel ?q ε)
            exact (Ne.isUnit (coe_ne_zero.mpr h))

open Convolution

@[simp] def shift (x : V) : 𝓓F ℝ V →L[ℝ] 𝓓F ℝ V := fromAutoOfV (shift' x)

lemma  ConvWithIsUniformContinuous-- [BorelSpace V]
   {k' : Type w}  [MeasureSpace k'] [NormedAddCommGroup k']  [NormedSpace ℝ k']
   {φ : 𝓓F ℝ V} {ψ : ℕ → V → k'} {ψ0 : V → k'} (hψ : TendstoUniformly ψ ψ0 atTop)
    {L : ℝ  →L[ℝ ] k' →L[ℝ] ℝ} :
    TendstoUniformly (β := ℝ) (fun n => (φ.φ ⋆[L] (ψ n))) ((φ.φ ⋆[L] ψ0)) atTop := by
      apply TendstoUniformly_iff_uniformZeroSeq.mpr
      --exact UniformContinuous.comp_tendstoUniformly (g:= fun ψ => φ.φ ⋆ ψ) ?_ ?_
      sorry
         /-
             I want to use somehow that (φ ⋆ _) is uniformly continuous (what is domain / codomain) to deduce that
              it preserve Uniform sequences.
            exact UniformContinuous.comp_tendstoUniformly (g:= fun ψ => φ.φ ⋆ ψ) ?_ this
            -/
lemma iteratedDerivConv {V : Type u}  [MeasureSpace V]
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
  · exact fun _ _ ↦ trivial
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
            exact φ.φHasCmpctSupport
            exact (ψ n).φHasCmpctSupport
          trans
          · exact this
          · apply add_subset_add_left
            exact hK.2 n



      · intro l
        induction' l with l hl -- ψ ψ0 hψ --
        · simp
          apply (zeroCase _).mpr
          exact ConvWithIsUniformContinuous ((zeroCase ℝ ).mp (hψ.2 0))
        · apply iteratedDerivConv
          exact ((zeroCase ℝ ).mp (hψ.2 0))


notation:67 φ " 𝓓⋆ " ψ => convWith φ ψ -- convolution𝓓Mult (tF2 φ ψ)
--@[simp] def convWith (φ : 𝓓 ℝ Ω ) : 𝓓 ℝ Ω →L[ℝ] 𝓓 ℝ Ω := ContinuousMultilinearMap.toContinuousLinearMap convolution𝓓Mult (tF2 φ 0) 1
notation:67 T " °⋆ " φ => ( convWith  (reflection φ) ) ° T

example  (φ : 𝓓F ℝ V ) (T : 𝓓' ℝ (Full V) ) : ∀ ψ, (T °⋆ φ) ψ = T ( φʳ 𝓓⋆ ψ) := fun _ => rfl
lemma convAsLambda (φ ψ : 𝓓F ℝ V) : (φ 𝓓⋆ ψ) = fun x => Λ (φ : LocallyIntegrableFunction V) (shift x (reflection ψ)) := by
  simp
  unfold convolution
  congr


theorem integral_congr {f g : V → ℝ} (p : ∀ x , f x = g x) : ∫ x , f x = ∫ x , g x := by congr ; ext x ; exact p x

-- def smoothFuncForConv (ψ : 𝓓F ℝ V ) :  (𝓓F ℝ V) :=
theorem convolution𝓓'IsSmooth (ψ : 𝓓F ℝ V ) (T : 𝓓'F ℝ V ) : ∃ ψ' , ContDiff ℝ ⊤ ψ'.f ∧ (T °⋆ ψ) = Λ ψ' := by

  let ψ' : LocallyIntegrableFunction V := ⟨ fun x =>T (shift x (reflection ψ)) , by sorry ⟩

  use ⟨ ψ' , by sorry ⟩
  constructor
  · let ζ := reflection ψ
    let ρ : V → 𝓓F ℝ V := fun  x => shift x ζ
    have : ψ'.f = T ∘ ρ := rfl

    have SeqContℕψ' {x : ℕ → V} {x0 : V} (hx : Tendsto x atTop (𝓝 x0)) : Tendsto (ψ'.f ∘ x) atTop (𝓝 (ψ'.f x0)) := by
      apply (SeqContinuous'OfContinuous ℝ T).seqCont
      have : (fun n => shift (x n) ζ) ⟶ shift x0 ζ := by sorry
      exact this
    have cont : Continuous ψ'.f := by sorry --help
    rw [this]
    --help, Do you suggest to define Distributions on all of V → k to be 0 if the input is not a test function?

    --apply ContDiff.comp
    -- · apply ContinuousLinearMap.contDiff
    -- · sorry --smoothness
    sorry
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
            rw [← integral_sub_right_eq_self (g:=y) ]
            ring_nf
            sorry


-- #lint
