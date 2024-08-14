import BonnAnalysis.Distributions.OfVEndo


namespace MeasureTheory
open MeasureTheory
open scoped Pointwise
universe  v w u u' v' -- u' is assumed to be ≤ u
open Order Set

open scoped Classical
open NNReal Topology
open Filter

open scoped Topology
open TopologicalSpace
noncomputable section
open Function
open Convolution

variable  {V : Type u}
    [MeasureSpace V]
   [NormedAddCommGroup V]  [NormedSpace ℝ V] --[ProperSpace V]
    [MeasureTheory.Measure.IsAddHaarMeasure (volume : Measure V)] [BorelSpace V] {Ω : Opens V} [T2Space V]  [SecondCountableTopology V] [LocallyCompactSpace V]
 [BorelSpace V]
    {k' : Type u'}   [NormedAddCommGroup k']  [NormedSpace ℝ k']
    {L : ℝ  →L[ℝ ] k' →L[ℝ] k'}
   {φ : 𝓓F ℝ V}-- {ψ0 : V → k'} {ψ0' : V → k'}

lemma TendstoUniformly_iff_uniformZeroSeq.{l} {k : Type l} [UniformSpace k] [AddGroup k] [UniformAddGroup k] {φ  : ℕ → V → k} {φ₀ : V → k} : TendstoUniformly φ φ₀ atTop ↔ TendstoUniformly (fun n => φ n - φ₀) 0 atTop := by
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

lemma convolutionWithConstFunc {φ : V → ℝ} (c : ℝ) : (φ ⋆ (fun _ => c)) = fun _ => (∫ v , φ v) * c := by
  unfold convolution
  ext x
  symm ;
  trans (∫ (v : V), c*  (φ v) )
  · symm ; rw [mul_comm] ; exact  (integral_smul c φ)
  · simp only [smul_eq_mul, ContinuousLinearMap.lsmul_apply] ; simp_rw [mul_comm] ;

lemma zeroSeqUniformly {a : ℕ → (V → k')} {α : ℕ → V → ENNReal} {C : ℝ≥0}
  (ha : ∀ n x , ‖ a n x‖ ≤ (α n x).toReal * C )
  (hα : TendstoUniformly (fun n x => (α n x).toReal) 0 atTop) : TendstoUniformly a 0 atTop := by

      rw [ TendstoUniformly_iff_uniformZeroSeq]
      rw [Metric.tendstoUniformly_iff] at hα
      simp_rw [ eventually_atTop ] at hα
      simp_rw [ ← tendstoUniformlyOn_univ , SeminormedAddGroup.tendstoUniformlyOn_zero, eventually_atTop ]
      intro ε hε

      by_cases h : C = 0
      · use 0 ; intro b _ ;
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
  ∀ ε > 0 , ∃ a, ∀ n ≥ a, || fun x => (φ n) x - φ₀ x ||_∞.toReal < ε := by
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


@[continuity] lemma ContCompactSupp.continuous (ψ0 : ContCompactSupp ℝ V k' ) : Continuous ψ0 :=  by apply ContDiff.continuous (𝕜:=ℝ ) ; exact ψ0.smooth

lemma convOfCtsCmpctSupportExists {φ : LocallyIntegrableFunction V}  (ψ : ContCompactSupp ℝ V k')  : ConvolutionExists φ.f ψ L := by
  intro x ;
  apply HasCompactSupport.convolutionExists_right -- HasCompactSupport.convolutionExistsAt
  exact ψ.hsupp --  --HasCompactSupport.convolution φ.fHasCmpctSupport
  exact φ.hf -- exact testFunctionIsLocallyIntegrable V φ
  exact ψ.continuous



lemma norm_convolution_le {x} {φ : 𝓓F ℝ V} (ψ0 : ContCompactSupp ℝ V k' ) : ‖ (φ ⋆[L] ψ0) x‖ ≤ ‖L‖ * ( (fun x => ‖ φ x‖) ⋆ (fun x => ‖ ψ0 x‖) ) x := by
        unfold convolution
        have {x y : V} : ‖ L (φ x) (ψ0 y)‖ ≤ ‖L‖ * ‖ φ x‖ * ‖ ψ0 y‖ := by
          trans ‖ L (φ x)‖ * ‖ ψ0 y‖
          · apply ContinuousLinearMap.le_opNorm
          · gcongr ; apply ContinuousLinearMap.le_opNorm
        calc
          ‖ (φ ⋆[L] ψ0) x‖ ≤ (∫⁻ (a : V), ENNReal.ofReal ‖ L (φ a) (ψ0 (x - a))‖).toReal := by apply MeasureTheory.norm_integral_le_lintegral_norm
          _ ≤ (∫⁻ (t : V), ENNReal.ofReal (‖L‖ *  ‖φ t‖ * ‖ψ0 (x-t)‖)).toReal := ?_  -- simp_rw [norm_mul]
          _ = ∫ (t : V),  ‖L‖ • (‖φ t‖ * ‖ψ0 (x-t)‖) := ?_
          _ = ‖L‖ • ∫ (t : V),  ‖φ t‖ * ‖ψ0 (x-t)‖ := by apply integral_smul
      --∫ (t : V),  ‖φ t‖ * ‖ψ0 (x-t)‖ =  ∫ (t : V), ((ContinuousLinearMap.lsmul ℝ ℝ) ((fun x ↦ ‖φ x‖) t)) ((fun x ↦ ‖ψ0 x‖) (x - t)) := by rfl
        · gcongr ;
          · rw [← lt_top_iff_ne_top] ;
            apply MeasureTheory.Integrable.lintegral_lt_top

            apply Continuous.integrable_of_hasCompactSupport
            have : Continuous φ.f := φ.continuous
            have : Continuous ψ0.f := ψ0.continuous
            continuity
            apply HasCompactSupport.mul_right  --(f:= fun _ => ‖L‖ )
            apply HasCompactSupport.mul_left
            apply HasCompactSupport.norm
            exact φ.hsupp




          · exact this
        · rw [← MeasureTheory.integral_toReal]
          · congr ; ext a ; simp only [smul_eq_mul] ;
            rw [mul_assoc , ENNReal.toReal_ofReal_eq_iff] ;
            apply mul_nonneg ;
            · apply ContinuousLinearMap.opNorm_nonneg
            · apply mul_nonneg ;
              · apply norm_nonneg
              · apply norm_nonneg  -- exact norm_nonneg _
          · apply AEMeasurable.ennreal_ofReal ;  -- I DONT KNOW HOW TO FIX THIS, because k' is not a measurable space in general (we want things like V →L[ℝ] ℝ) -- apply AEMeasurable.norm ; apply AEMeasurable.mul  ;
            ·
              apply AEMeasurable.mul
              · apply AEMeasurable.mul  ;
                · measurability ;
                ·
                  apply AEMeasurable.norm
                  apply Continuous.aemeasurable
                  apply ContDiff.continuous (𝕜:=ℝ ) (φ.smooth) ;




              · apply Continuous.aemeasurable
                apply Continuous.norm

                continuity


          · apply ae_of_all
            intro _
            exact ENNReal.ofReal_lt_top



open ContinuousLinearMap
variable {G : Type* } {x : G} [MeasureSpace G] {μ : Measure G}
  [AddGroup G] [ MeasurableAdd₂ G] [  SigmaFinite μ] [ MeasurableNeg G] [  μ.IsAddLeftInvariant]



theorem convolution_mono_right_ae {f g g' : G → ℝ} (hfg : ConvolutionExistsAt f g x (lsmul ℝ ℝ) μ)
    (hfg' : ConvolutionExistsAt f g' x (lsmul ℝ ℝ) μ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ᵐ  (x : G) ∂μ, g x ≤ g' x) :
    (f ⋆[lsmul ℝ ℝ, μ] g) x ≤ (f ⋆[lsmul ℝ ℝ, μ] g') x := by
  apply integral_mono_ae hfg hfg'
  simp only [lsmul_apply, Algebra.id.smul_eq_mul]
  unfold EventuallyLE

  have hg : {t | g (x - t) ≤ g' (x-t)} ∈ ae μ := by
    have :  {t | g (x - t) ≤ g' (x-t)} = (fun t => x - t) ⁻¹' {t | g t ≤ g' t} := by rfl -- ext t ; simp ; constructor ; intro h ; use x - t; exact ⟨ h , simp ⟩  ; intro h ; obtain ⟨ x' , hx' ⟩ := h ; rw [show x = x' + t from ?_]  ; exact hx'.1
    rw [this]
    rw [ae_iff] at hg
    rw [mem_ae_iff ,← Set.preimage_compl]
    apply MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null
    apply MeasureTheory.quasiMeasurePreserving_sub_left
    exact hg



  have {x t} : g (x - t) ≤ g' (x-t) →  f t * g (x - t) ≤ f t * g' (x-t) := by
    intro h
    apply mul_le_mul_of_nonneg_left h (hf _)
  rw [Filter.eventually_iff]

  -- have hg : {x | g (x - t) ≤ g' (x-t)} ∈ ae μ

  apply sets_of_superset
  ·
    exact hg
  · intro t ht ; apply this ht
  -- simp_rw [ ]

  -- intro t
lemma convolution_mono_right_of_nonneg_ae  {f g g' : G → ℝ} (hfg' : ConvolutionExistsAt f g' x (ContinuousLinearMap.lsmul ℝ ℝ) μ)
  (hf : ∀ (x : G), 0 ≤ f x) (hg : ∀ᵐ (x : G) ∂ μ, g x ≤ g' x) (hg' : ∀ (x : G), 0 ≤ g' x) :
  (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) x ≤ (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g') x :=
  by
  by_cases H : ConvolutionExistsAt f g x (lsmul ℝ ℝ) μ
  · exact convolution_mono_right_ae H hfg' hf hg
  have : (f ⋆[lsmul ℝ ℝ, μ] g) x = 0 := integral_undef H
  rw [this]
  exact integral_nonneg fun y => mul_nonneg (hf y) (hg' (x - y))
variable  {ψ : ℕ → ContCompactSupp ℝ V k'} {ψ0 : ContCompactSupp ℝ V k'} (hψ : ψ ⟶ ψ0) --TendstoUniformly (fun n => (ψ n)) ψ0 atTop) (KhK : ∃ K : Set V , IsCompact K ∧ ∀ n , tsupport (ψ n) ⊆ K)

lemma  ConvWithIsUniformContinuous
     :
    TendstoUniformly (β := k') (fun n => (φ.f ⋆[L] (ψ n))) ((φ.f ⋆[L] ψ0)) atTop := by
      apply TendstoUniformly_iff_uniformZeroSeq.mpr
      --exact UniformContinuous.comp_tendstoUniformly (g:= fun ψ => φ.f ⋆ ψ) ?_ ?_
      rw [show  (fun n ↦ φ.f ⋆[L] ψ n - φ.f ⋆[L] ψ0) = fun n ↦ φ.f ⋆[L] (ψ n - ψ0) from ?_] ; swap
      · ext1 n ;
        rw [show (ψ n - ψ0).f = ((ψ n).f + (((-1 : ℝ) • ψ0).f)) from ?_]
        ext x

        rw [ConvolutionExistsAt.distrib_add, sub_eq_add_neg]
        simp only [Pi.add_apply, Pi.neg_apply, add_right_inj]
        apply congrFun (a:=x)
        trans (-1 : ℝ) • (φ.f ⋆[L] ψ0); swap
        · symm ; exact convolution_smul
        · ext x ; simp only [Pi.smul_apply, smul_eq_mul, neg_mul, one_mul, neg_smul, one_smul]
        · apply convOfCtsCmpctSupportExists (φ := (φ : LocallyIntegrableFunction V))
        · apply convOfCtsCmpctSupportExists  (φ := (φ : LocallyIntegrableFunction V))
        · simp only [instAddCommGroupContCompactSupp, instNegContCompactSupp,
          instSMulContCompactSupp] ; ext x ; simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply] ; simp ;  apply sub_eq_add_neg (a := (ψ n) x) (b:= ψ0 x)
      · let C : ℝ≥0 := ⟨ ‖L‖ *  ∫  v , ‖ φ v‖ , by apply mul_nonneg ; apply ContinuousLinearMap.opNorm_nonneg ; apply integral_nonneg ; intro _ ; apply norm_nonneg  ⟩
        have : ∀ n x , ‖ (φ.f ⋆[L] (ψ n - ψ0)) x‖ ≤ || ψ n - ψ0 ||_∞.toReal * C.1  := by
          intro n x

          calc
            ‖ (φ.f ⋆[L] (ψ n - ψ0)) x‖  ≤ ‖L‖ * ((fun x => ‖φ.f x‖) ⋆ (fun x => ‖ (ψ n - ψ0) x‖ )) x := norm_convolution_le (φ := φ) (ψ0 := ψ n - ψ0)
            _ ≤  ‖L‖ * ((fun x => ‖φ.f x‖) ⋆ (fun _ => || ψ n - ψ0 ||_∞.toReal )) x  := ?_
            _ = ‖L‖ * ((∫  v , ‖ φ v‖) * || ψ n - ψ0 ||_∞.toReal) := by apply congrArg ; apply congrFun ; apply convolutionWithConstFunc
            _ ≤ || ψ n - ψ0 ||_∞.toReal * (‖L‖ *  ∫ v , ‖ φ v‖)  := by rw [← mul_assoc , mul_comm]

          gcongr
          apply convolution_mono_right_of_nonneg_ae
          · apply HasCompactSupport.convolutionExists_left_of_continuous_right ;
            · refine (hasCompactSupport_comp_left (g:= fun x => ‖x‖) (f:= φ.f) ?_).mpr ?_ ;
              · intro _ ; exact norm_eq_zero ;
              · exact φ.hsupp
            · rw [← MeasureTheory.locallyIntegrableOn_univ] ; apply MeasureTheory.LocallyIntegrableOn.norm ; rw [MeasureTheory.locallyIntegrableOn_univ] ; apply testFunctionIsLocallyIntegrable -- apply testFunctionIsLocallyIntegrable
            · apply continuous_const ;
          · intro x ; apply norm_nonneg ;
          · have {x} :  ‖(ψ n - ψ0) x‖ ≤ || ψ n - ψ0 ||_∞.toReal ↔  ENNReal.ofReal ‖(ψ n - ψ0) x‖ ≤ || ψ n - ψ0 ||_∞ := by
              symm
              apply ENNReal.ofReal_le_iff_le_toReal
              rw [← lt_top_iff_ne_top]
              apply EssSupTestFunction
            simp_rw [this]
            simp_rw [ofReal_norm_eq_coe_nnnorm]
            apply ae_le_snormEssSup (f:=(ψ n - ψ0))
          · intro _ ; apply ENNReal.toReal_nonneg
        apply zeroSeqUniformly this
        rw [← tendstoUniformlyOn_univ]
        apply Filter.Tendsto.tendstoUniformlyOn_const
        apply NormedAddCommGroup.tendsto_nhds_zero.mpr
        have {x : ENNReal} : ‖x.toReal‖ = x.toReal :=  NNReal.norm_eq _
        simp_rw [ eventually_atTop , this, ccs_sub]
        apply EssSupNormSub (φ := fun n => (ψ n).f) (φ₀:= ψ0.f)
        apply (zeroCase _ ).mp (hψ.2 0)

lemma fderiv_convolution (ψ0 : ContCompactSupp ℝ V k') {φ : LocallyIntegrableFunction V} :
   fderiv ℝ (φ.f ⋆[L] ψ0) = φ.f ⋆[ContinuousLinearMap.precompR V L] (fderiv ℝ ψ0) := by
    ext1 x
    apply HasFDerivAt.fderiv
    apply HasCompactSupport.hasFDerivAt_convolution_right ;
    exact ψ0.hsupp
    exact φ.hf

    exact ContDiff.of_le (𝕜 := ℝ) (f:= ψ0) ψ0.smooth  (OrderTop.le_top 1)


open ContinuousMultilinearMap

variable
{k' : Type u}   [NormedAddCommGroup k']  [NormedSpace ℝ k']
  {V : Type u}
    [MeasureSpace V]
   [NormedAddCommGroup V]  [NormedSpace ℝ V] --[ProperSpace V]
    [MeasureTheory.Measure.IsAddHaarMeasure (volume : Measure V)] [BorelSpace V] [T2Space V]  [SecondCountableTopology V] [LocallyCompactSpace V]
 [BorelSpace V]

    {L : ℝ  →L[ℝ ] k' →L[ℝ] k'}
    {φ : 𝓓F ℝ V} {ψ : ℕ → ContCompactSupp ℝ V k'}  (ψ0 : ContCompactSupp ℝ V k' )
    (hψ : ψ ⟶ ψ0)

-- def T : Type max 1 u u' := V →L[ℝ] k'
--#check  : Type max 1 u u'
theorem iteratedDerivConv
    {φ : 𝓓F ℝ V}  {l : ℕ}
     :
    TendstoUniformly (fun n => iteratedFDeriv ℝ (l) (φ.f ⋆[L] (ψ n))) (iteratedFDeriv ℝ (l) (φ.f ⋆[L] ψ0)) atTop := by


      induction' l with l hl generalizing k' ψ ψ0 hψ L
      · apply (zeroCase _).mpr ; apply ConvWithIsUniformContinuous hψ
      · have {ψ0} :  iteratedFDeriv ℝ (l+1) (φ.f ⋆[L] (ψ0)) =
          fun z => (iteratedFDeriv ℝ (l) (fderiv ℝ (φ.f ⋆[L] (ψ0))) z).uncurryRight := by ext1 z ; exact iteratedFDeriv_succ_eq_comp_right

        have {ψ0 : ContCompactSupp ℝ V k'} :  iteratedFDeriv ℝ (l+1) (φ.f ⋆[L] (ψ0.f)) =
          fun z => (iteratedFDeriv ℝ (l) (φ ⋆[ContinuousLinearMap.precompR V L] (fderivCCS ψ0).f) z).uncurryRight := by
            rw [this] ;
            simp_rw [fderiv_convolution (φ := (φ : LocallyIntegrableFunction V)) (ψ0 := ψ0)] ;

            rfl
        -- have _ : := ⟨ hψ0 ,
        --   by apply ContCompactLimit (ψ := ψ) hψ KhK ⟩
        simp_rw [this  ]

        have moin : TendstoUniformly
            (fun n ↦ (iteratedFDeriv ℝ l (φ.f ⋆[ContinuousLinearMap.precompR V L, volume] fderiv ℝ (ψ n))))
            (iteratedFDeriv ℝ l (φ.f ⋆[ContinuousLinearMap.precompR V L, volume] ( fderivCCS ψ0 ).f)) atTop := by
              apply hl (k' := (V →L[ℝ] k' )) (ψ := fun n => fderivCCS (ψ n))  (L := ContinuousLinearMap.precompR V L)
              · apply SeqContinuousStronglyFderivCCS.seqCont
                exact hψ


        refine UniformContinuous.comp_tendstoUniformly (g:= (continuousMultilinearCurryRightEquiv' ℝ l V k')) ?_ moin
        exact Isometry.uniformContinuous (continuousMultilinearCurryRightEquiv' ℝ l V k').isometry

-- variable (ψ : V → k')
-- def ContCompactLimit : HasCompactSupport ψ := by

--     obtain ⟨ K , hK ⟩ := hψ.1
--     apply IsCompact.of_isClosed_subset ;
--     · exact hK.1
--     · exact isClosed_tsupport ψ0
--     · apply KcontainsSuppOfLimit'
--       intro p
--       refine TendstoUniformly.tendsto_at ((zeroCase _ ).mp (hψ.2 0)) hK
