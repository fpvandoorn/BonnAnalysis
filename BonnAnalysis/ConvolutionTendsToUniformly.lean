import Mathlib.Topology.Sequences
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order
import Mathlib.Topology.Algebra.ContinuousAffineMap
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
open Convolution
variable  {V : Type u}  [MeasureSpace V]
   [NormedAddCommGroup V]  [NormedSpace ℝ V] --[ProperSpace V]
    [MeasureTheory.Measure.IsAddHaarMeasure (volume : Measure V)] [BorelSpace V] {Ω : Opens V} [T2Space V]  [SecondCountableTopology V] [LocallyCompactSpace V]
 [BorelSpace V]
    {k' : Type u}   [NormedAddCommGroup k']  [NormedSpace ℝ k']  {L : ℝ  →L[ℝ ] k' →L[ℝ] k'}
   {φ : 𝓓F ℝ V} {ψ : ℕ → V → k'} {ψ0 : V → k'} (hψ : TendstoUniformly (fun n => (ψ n)) ψ0 atTop)
lemma TendstoUniformly_iff_uniformZeroSeq {k : Type v} [UniformSpace k] [AddGroup k] [UniformAddGroup k] {φ  : ℕ → V → k} {φ₀ : V → k} : TendstoUniformly φ φ₀ atTop ↔ TendstoUniformly (fun n => φ n - φ₀) 0 atTop := by
          constructor
          · intro hφ
            rw [show (0 = φ₀ - φ₀) from (by simp)]
            apply TendstoUniformly.sub hφ
            rw [← tendstoUniformlyOn_univ]
            apply CnstSeqTendstoUniformlyOn
          · intro hφ
            rw [show (φ = (fun n => φ n - φ₀ + φ₀)) from (by simp)]
            -- rw [show (φ₀ = 0 + φ₀) from (by simp)]
            have : TendstoUniformly (fun n ↦ (φ n - φ₀) + φ₀) ( 0 + φ₀) atTop := by
              apply TendstoUniformly.add hφ ;
              · rw [← tendstoUniformlyOn_univ]
                apply CnstSeqTendstoUniformlyOn φ₀ atTop ;
            rw [show 0 + φ₀ = φ₀ from (by simp)] at this
            exact this

lemma convolutionWithConstFunc {φ : V → ℝ} (c : k') : (φ ⋆[L] (fun _ => c)) = fun _ => L (∫ v , φ v) c := by
  unfold convolution
  ext x
  symm ;
  trans (∫ (v : V), L (φ v) c)
  · symm ; rw [mul_comm] ; exact  (integral_smul c φ)
  · simp only [smul_eq_mul, ContinuousLinearMap.lsmul_apply] ; simp_rw [mul_comm] ;

lemma zeroSeqUniformly {a : ℕ → (V → ℝ)} {α : ℕ → V → ENNReal} {C : ℝ≥0}
  (ha : ∀ n x , ‖ a n x‖ ≤ (α n x).toReal * C )
  (hα : TendstoUniformly (fun n x => (α n x).toReal) 0 atTop) : TendstoUniformly a (fun _ => 0) atTop := by

      rw [ TendstoUniformly_iff_uniformZeroSeq]
      rw [Metric.tendstoUniformly_iff] at hα
      simp_rw [ eventually_atTop ] at hα
      simp_rw [ ← tendstoUniformlyOn_univ , SeminormedAddGroup.tendstoUniformlyOn_zero, eventually_atTop ]
      intro ε hε

      by_cases h : C = 0
      · use 0 ; intro b hb ;
        intro x _
        apply LE.le.trans_lt
        · simp ; exact ha b x
        · have : ‖(α b x).toReal‖ * C   < ε := by
            rw [h] ;
            simp
            exact hε
          rw [show  ‖(α b x).toReal‖ = (α b x).toReal from NNReal.norm_eq _] at this
          exact this
      · let ε' : ℝ := ε / C
        -- have hε' : ε' > 0 ∧
        have hC : 0 < C := pos_iff_ne_zero.mpr h
        obtain ⟨ m , hm ⟩ :=  hα ε' (by apply (div_pos_iff_of_pos_right ?_).mpr ; exact hε ;   exact hC  )
        use m

        intro b hb x _
        specialize hm b hb x
        apply LE.le.trans_lt
        · simp ; exact ha b x
        · rw [show (ε = ε' * C ) from ?_]
          · apply (mul_lt_mul_right ?_ ).mpr
            simp only [Pi.zero_apply, dist_zero_left, Real.norm_eq_abs, ENNReal.abs_toReal] at hm
            exact hm
            exact hC
          · refine Eq.symm (IsUnit.div_mul_cancel ?q _)
            exact (Ne.isUnit (coe_ne_zero.mpr h))
lemma EssSupNormSub {φ : ℕ → V → k'} {φ₀ : V → k' } (hφ : TendstoUniformly φ φ₀ atTop) :
  ∀ ε > 0 , ∃ a, ∀ n ≥ a, || φ n - φ₀ ||_∞.toReal < ε := by
        have : ∀ ε > 0 , ∃ a, ∀ n ≥ a,  ∀ x ∈ univ , ‖((φ n) - φ₀) x‖ < ε := by
          simp_rw [← eventually_atTop  ]


          have : TendstoUniformly (fun n => (φ n) - φ₀) 0 atTop := by apply TendstoUniformly_iff_uniformZeroSeq.mp hφ

          apply SeminormedAddGroup.tendstoUniformlyOn_zero.mp (tendstoUniformlyOn_univ.mpr this)
        intro ε hε
        obtain ⟨ a , ha ⟩ := this (ε / 2) (half_pos hε ) -- hε
        use a
        intro n hn
        have foo {ε} {ψ : V → k'} (hε : ε ≥ 0) (p : ∀ x ∈ univ , ‖ ψ x‖  < ε) : || ψ ||_∞.toReal ≤ ε   := by
          have : || ψ ||_∞ ≤ ENNReal.ofReal ε := by
            apply MeasureTheory.snormEssSup_le_of_ae_bound (C:=ε)
            apply ae_of_all volume
            intro a
            apply le_of_lt
            exact p a trivial
          refine ENNReal.toReal_le_of_le_ofReal hε  this
        apply LE.le.trans_lt
        · exact foo (ε := ε / 2) (ψ := fun x => (φ n x) - φ₀ x) (le_of_lt (half_pos hε)) (ha n hn)
        · exact div_two_lt_of_pos hε

--------------------------------------------------------
class ContCompactSupp (f : V → k') where
  cont : Continuous f
  hsupp : HasCompactSupport f
  cdiff : ContDiff ℝ 1 f
open ContCompactSupp

lemma convOfCtsCmpctSupportExists {φ : LocallyIntegrableFunction V} {ψ : V → k' } [ContCompactSupp ψ]  : ConvolutionExists φ.f ψ L := by
  intro x ;
  apply HasCompactSupport.convolutionExists_right -- HasCompactSupport.convolutionExistsAt
  exact hsupp --  --HasCompactSupport.convolution φ.φHasCmpctSupport
  exact φ.hf -- exact testFunctionIsLocallyIntegrable V φ
  apply cont --



lemma norm_convolution_le {x} {φ : V → ℝ} {ψ : V → k'}  : ‖ (φ ⋆[L] ψ) x‖ ≤ ( (fun x => ‖ φ x‖) ⋆ (fun x => ‖ ψ x‖) ) x := by
        unfold convolution
        calc
          ‖ (φ ⋆[L] ψ) x‖ ≤ (∫⁻ (a : V), ENNReal.ofReal ‖ L (φ a) (ψ (x - a))‖).toReal := by apply MeasureTheory.norm_integral_le_lintegral_norm
          _ ≤ ∫ (t : V),  ‖L (φ t) (ψ (x-t))‖ := ?_
          _ = ∫ (t : V),  ‖φ t‖ * ‖ψ (x-t)‖ := by sorry -- simp_rw [norm_mul]
      --∫ (t : V),  ‖φ t‖ * ‖ψ (x-t)‖ =  ∫ (t : V), ((ContinuousLinearMap.lsmul ℝ ℝ) ((fun x ↦ ‖φ x‖) t)) ((fun x ↦ ‖ψ x‖) (x - t)) := by rfl
        · rw [← MeasureTheory.integral_toReal]
          · apply le_of_eq ; congr ; ext a ; rw [ENNReal.toReal_ofReal_eq_iff] ; exact norm_nonneg (φ a * ψ (x - a))
          · apply AEMeasurable.ennreal_ofReal ; apply AEMeasurable.norm ; apply AEMeasurable.mul  ;
            · apply MeasureTheory.AEStronglyMeasurable.aemeasurable ; exact testFunctionMeasurable
            · sorry
            -- · rw [show (fun a ↦ ψ.φ (x - a)) = (fun a ↦ (ψʳ).φ (a - x)) from ?_ ]
            --   apply MeasureTheory.AEStronglyMeasurable.aemeasurable ; exact testFunctionMeasurable (φ := (shift x) (ψʳ ))
            --   ext a ;
            --   simp only [instAddCommGroup𝓓, instNeg𝓓, reflection, fromEndoOfV, mk, reflection',
            --     ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousLinearMap.coe_mk',
            --     LinearMap.coe_mk, AddHom.coe_mk, comp_apply, _root_.map_sub,
            --     ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_id', id_eq, sub_neg_eq_add]
            --   congr
            --   exact sub_eq_neg_add x a
          · apply ae_of_all
            intro _
            exact ENNReal.ofReal_lt_top


instance [ContCompactSupp ψ0] (c : ℝ) : ContCompactSupp (c • ψ0) where
  cont := by sorry
  hsupp := by sorry
lemma  ConvWithIsUniformContinuous [∀ n , ContCompactSupp (ψ n)] [ContCompactSupp ψ0]
     :
    TendstoUniformly (β := k') (fun n => (φ.φ ⋆[L] (ψ n))) ((φ.φ ⋆[L] ψ0)) atTop := by
      apply TendstoUniformly_iff_uniformZeroSeq.mpr
      --exact UniformContinuous.comp_tendstoUniformly (g:= fun ψ => φ.φ ⋆ ψ) ?_ ?_
      rw [show  (fun n ↦ φ.φ ⋆[L] ψ n - φ.φ ⋆[L] ψ0) = fun n ↦ φ.φ ⋆[L] (ψ n - ψ0) from ?_] ; swap
      · ext1 n ;
        rw [show (ψ n - ψ0) = ((ψ n) + (((-1 : ℝ) • ψ0))) from ?_]
        ext x

        rw [ConvolutionExistsAt.distrib_add, sub_eq_add_neg]
        simp only [Pi.add_apply, Pi.neg_apply, add_right_inj]
        apply congrFun (a:=x)
        trans (-1 : ℝ) • (φ.φ ⋆[L] ψ0); swap
        · symm ; exact convolution_smul
        · ext x ; simp only [Pi.smul_apply, smul_eq_mul, neg_mul, one_mul] ; sorry
        · apply convOfCtsCmpctSupportExists (φ := (φ : LocallyIntegrableFunction V))
        · apply convOfCtsCmpctSupportExists  (φ := (φ : LocallyIntegrableFunction V))   --(ψ := (-1) • φ0)
        · simp only [instAddCommGroup𝓓, instNeg𝓓, neg_smul, one_smul] ; ext x ; sorry
      · have : ∀ n x , ‖ (φ.φ ⋆[L] (ψ n - ψ0)) x‖ ≤ || ψ n - ψ0 ||_∞.toReal * (⟨ ∫  v , ‖ φ v‖ , by apply integral_nonneg ; intro _ ; apply norm_nonneg  ⟩ : ℝ≥0).1  := by
          intro n x

          calc
            ‖ (φ.φ ⋆[L] (ψ n - ψ0)) x‖  ≤ _ := norm_convolution_le (φ := φ) (ψ := ψ n - ψ0)
            _ ≤  ((fun x => ‖φ.φ x‖) ⋆ (fun _ => || ψ n - ψ0 ||_∞.toReal )) x  := ?_
            _ ≤  (∫  v , ‖ φ v‖) * || ψ n - ψ0 ||_∞.toReal := by apply le_of_eq ; apply congrFun ; apply convolutionWithConstFunc
            _ ≤   || ψ n - ψ0 ||_∞.toReal * (∫ v , ‖ φ v‖)  := by rw [mul_comm]
          apply convolution_mono_right_of_nonneg
          · apply HasCompactSupport.convolutionExists_left_of_continuous_right ;
            · refine (hasCompactSupport_comp_left (g:= fun x => ‖x‖) (f:= φ.φ) ?_).mpr ?_ ;
              · intro _ ; exact norm_eq_zero ;
              · exact φ.φHasCmpctSupport
            · rw [← MeasureTheory.locallyIntegrableOn_univ] ; apply MeasureTheory.LocallyIntegrableOn.norm ; rw [MeasureTheory.locallyIntegrableOn_univ] ; sorry -- apply testFunctionIsLocallyIntegrable
            · apply continuous_const ; --apply convolutionExistsAt_flip.mpr ;
          · intro x ; apply norm_nonneg ;
          · sorry
          · intro _ ; apply ENNReal.toReal_nonneg

        refine zeroSeqUniformly (α := fun n x => || ψ n - ψ0 ||_∞ )  this ?_
        rw [← tendstoUniformlyOn_univ]
        apply Filter.Tendsto.tendstoUniformlyOn_const
        apply NormedAddCommGroup.tendsto_nhds_zero.mpr
        have {x : ENNReal} : ‖x.toReal‖ = x.toReal :=  NNReal.norm_eq _

        simp_rw [ eventually_atTop , this]

        exact EssSupNormSub (φ := ψ) (φ₀:= ψ0) hψ


         /-
             I want to use somehow that (φ ⋆ _) is uniformly continuous (what is domain / codomain) to deduce that
              it preserve Uniform sequences.
            exact UniformContinuous.comp_tendstoUniformly (g:= fun ψ => φ.φ ⋆ ψ) ?_ this
            -/
instance [ContCompactSupp ψ0]: ContCompactSupp (fderiv ℝ ψ0) where
  cont := by sorry
  hsupp := by sorry
  cdiff := by sorry
lemma fderiv_convolution [ ContCompactSupp ψ0] {φ : LocallyIntegrableFunction V} :
   fderiv ℝ (φ.f ⋆[L] ψ0) = φ.f ⋆[ContinuousLinearMap.precompR V L] (fderiv ℝ ψ0) := by sorry -- apply HasCompactSupport.hasFDerivAt_convolution_right ;
open ContinuousMultilinearMap
theorem iteratedDerivConv
    {φ : 𝓓F ℝ V}   [∀ n , ContCompactSupp (ψ n)] [ContCompactSupp ψ0]  {l : ℕ}
     :
    TendstoUniformly (fun n => iteratedFDeriv ℝ (l) (φ.φ ⋆[L] (ψ n))) (iteratedFDeriv ℝ (l) (φ.φ ⋆[L] ψ0)) atTop := by
      induction' l with l hl generalizing k' ψ ψ0 hψ L
      · sorry
      · have {ψ0} :  iteratedFDeriv ℝ (l+1) (φ.φ ⋆[L] (ψ0)) =
          fun z => (iteratedFDeriv ℝ (l) (fderiv ℝ (φ.φ ⋆[L] (ψ0))) z).uncurryRight := by ext1 z ; exact iteratedFDeriv_succ_eq_comp_right
        have {ψ0} [ ContCompactSupp ψ0] :  iteratedFDeriv ℝ (l+1) (φ.φ ⋆[L] (ψ0)) =
          fun z => (iteratedFDeriv ℝ (l) (φ ⋆[ContinuousLinearMap.precompR V L] (fderiv ℝ ψ0)) z).uncurryRight := by
            rw [this] ;
            simp_rw [fderiv_convolution (φ := (φ : LocallyIntegrableFunction V)) (ψ0 := ψ0)] ;
        simp_rw [this]
        have moin : TendstoUniformly
            (fun n ↦ (iteratedFDeriv ℝ l (φ.φ ⋆[ContinuousLinearMap.precompR V L, volume] fderiv ℝ (ψ n))))
            (iteratedFDeriv ℝ l (φ.φ ⋆[ContinuousLinearMap.precompR V L, volume] fderiv ℝ ψ0)) atTop := by
              apply hl (k' := V →L[ℝ] k') (ψ := fun n => fderiv ℝ (ψ n))  (L := ContinuousLinearMap.precompR V L)
              sorry
        refine UniformContinuous.comp_tendstoUniformly (g:= (continuousMultilinearCurryRightEquiv' ℝ l V k')) ?_ moin
        exact Isometry.uniformContinuous (continuousMultilinearCurryRightEquiv' ℝ l V k').isometry
