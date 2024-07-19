import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import BonnAnalysis.StrongType
import Mathlib.Analysis.Convolution

noncomputable section

open FourierTransform MeasureTheory Real Lp Memℒp Filter Complex Topology ComplexInnerProductSpace ComplexConjugate

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V]


lemma fourier_conj {f : V → ℂ} : 𝓕 (conj f) = conj (𝓕 (f ∘ (fun x ↦ -x))) := by
  unfold fourierIntegral VectorFourier.fourierIntegral
  ext w
  simp
  rw [← integral_conj, ← integral_neg_eq_self]
  apply congrArg (integral volume)
  ext v
  rw [show 𝐞 (-⟪v, w⟫_ℝ) • f (-v) = 𝐞 (-⟪v, w⟫_ℝ) * f (-v) from rfl, starRingEnd_apply, starRingEnd_apply, star_mul']
  rw [show 𝐞 (-⟪-v, w⟫_ℝ) • star (f (-v)) = 𝐞 (-⟪-v, w⟫_ℝ) * star (f (-v)) from rfl]
  simp
  left
  unfold Real.fourierChar
  simp [← Complex.exp_conj, Complex.exp_neg, inv_inv, conj_ofReal]




lemma fourier_convolution {f g : V → ℂ} (hf : Integrable f volume) (hg : Integrable g volume) :
    𝓕 (convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume) = (𝓕 f) * (𝓕 g) := by
  unfold convolution fourierIntegral VectorFourier.fourierIntegral
  simp
  ext x
  simp
  symm
  calc (∫ (v : V), 𝐞 (-⟪v, x⟫_ℝ) • f v) * ∫ (v : V), 𝐞 (-⟪v, x⟫_ℝ) • g v
    _ = ∫ (v : V), 𝐞 (-⟪v, x⟫_ℝ) • f v * ∫ (w : V), 𝐞 (-⟪w, x⟫_ℝ) • g w := Eq.symm (integral_mul_right _ _)
    _ = ∫ (v : V), 𝐞 (-⟪v, x⟫_ℝ) • f v * ∫ (w : V), 𝐞 (-⟪w - v,x⟫_ℝ) • g (w - v) := ?_
    _ = ∫ (v : V) (w : V), 𝐞 (-⟪v, x⟫_ℝ) * 𝐞 (-⟪w - v,x⟫_ℝ) * (f v * g (w - v)) := ?_
    _ = ∫ (v : V) (w : V), 𝐞 (-⟪w, x⟫_ℝ) * (f v * g (w - v)) := ?_
    _ = ∫ (w : V) (v : V), 𝐞 (-⟪w, x⟫_ℝ) * (f v * g (w - v)) := ?_
    _ = ∫ (w : V), 𝐞 (-⟪w, x⟫_ℝ) * ∫ (v : V), f v * g (w - v) :=
        congrArg (integral volume) <| (Set.eqOn_univ _ _).1 fun _ _ ↦ integral_mul_left _ _
    _ = ∫ (v : V), 𝐞 (-⟪v, x⟫_ℝ) • ∫ (t : V), f t * g (v - t) := rfl
  · apply congrArg (integral volume)
    ext v
    simp
    left
    exact (integral_sub_right_eq_self (fun w ↦ 𝐞 (-⟪w,x⟫_ℝ) • g w) v).symm
  · apply congrArg (integral volume)
    ext v
    rw [← integral_mul_left]
    apply congrArg (integral volume)
    ext w
    rw [show  𝐞 (-⟪v, x⟫_ℝ) • f v = 𝐞 (-⟪v, x⟫_ℝ) * f v  from rfl ,
        show 𝐞 (-⟪w - v, x⟫_ℝ) • g (w - v) = 𝐞 (-⟪w - v, x⟫_ℝ) * g (w - v) from rfl]
    ring
  · apply congrArg (integral volume)
    ext v
    apply congrArg (integral volume)
    ext w
    apply mul_eq_mul_right_iff.2
    left
    unfold Real.fourierChar
    simp only [AddChar.coe_mk, mul_neg, coe_inv_unitSphere, expMapCircle_apply, ofReal_mul, ofReal_ofNat]
    rw [← Complex.exp_add]
    apply congrArg (cexp)
    simp

    rw [show ⟪w, x⟫_ℝ = ⟪v, x⟫_ℝ + ⟪w - v, x⟫_ℝ from
        by rw [← InnerProductSpace.add_left, add_sub_cancel]]

    push_cast
    ring
  · apply integral_integral_swap
    rw [integrable_prod_iff]
    constructor
    · simp
      apply ae_of_all volume
      intro v
      have h : AEStronglyMeasurable (fun a ↦ f v * g (a - v)) volume := by
        apply AEStronglyMeasurable.mul aestronglyMeasurable_const
        apply AEStronglyMeasurable.comp_measurePreserving (Integrable.aestronglyMeasurable hg)
        exact measurePreserving_sub_right volume v
      apply (integrable_norm_iff ?_).1
      have : (∀ b, (fun a ↦ ‖(𝐞 (-⟪a,x⟫_ℝ) : ℂ) * (f v * g (a - v))‖) b = (fun a ↦ ‖f v * g (a - v)‖) b) := by
        simp
      apply (integrable_congr (ae_of_all volume this)).2
      apply (integrable_norm_iff h).2
      apply Integrable.const_mul
      exact Integrable.comp_sub_right hg v
      apply AEStronglyMeasurable.mul; swap; exact h
      rw [show  (fun y ↦ ↑(𝐞 (-⟪y, x⟫_ℝ))) = (Complex.exp ∘ ((- 2 * (π : ℂ) * I) • (fun y ↦ (⟪y, x⟫_ℝ : ℂ)))) from ?_] ; swap
      ext y
      unfold Real.fourierChar
      simp[Complex.exp_neg]
      exact congrArg cexp (by ring)
      apply aestronglyMeasurable_iff_aemeasurable.2
      apply Measurable.comp_aemeasurable Complex.measurable_exp
      apply AEMeasurable.const_smul (Continuous.aemeasurable ?_)
      rw [show  (fun y ↦ (⟪y, x⟫_ℝ : ℂ)) = ((fun x ↦ (x : ℂ)) : ℝ → ℂ) ∘ ((fun y ↦ ⟪y, x⟫_ℝ) : V → ℝ) from ?_] ; swap
      ext y; simp
      exact Continuous.comp continuous_ofReal (Continuous.inner continuous_id' continuous_const)
    · simp

      rw [show (fun x ↦ ∫ (y : V), Complex.abs (f x) * Complex.abs (g (y - x))) = (fun x ↦ ‖f x‖ * ∫ (y : V), Complex.abs (g y)) from ?_] ; swap
      ext x
      rw [← integral_add_right_eq_self _ x]
      simp
      exact integral_mul_left (Complex.abs (f x)) fun a ↦ Complex.abs (g a)
      apply Integrable.mul_const
      apply (integrable_norm_iff ?_).2
      exact hf
      exact Integrable.aestronglyMeasurable hf
    · apply AEStronglyMeasurable.mul
      have : AEStronglyMeasurable (fun a ↦ (𝐞 (-⟪a, x⟫_ℝ) : ℂ)) volume := by
        unfold Real.fourierChar
        simp
        apply aestronglyMeasurable_iff_aemeasurable.2
        apply Measurable.comp_aemeasurable measurable_inv
        apply Measurable.comp_aemeasurable Complex.measurable_exp
        apply AEMeasurable.mul_const _ I
        apply AEMeasurable.const_mul
        apply Continuous.aemeasurable
        rw [show (fun y ↦ (⟪y, x⟫_ℝ : ℂ)) = ((fun x ↦ (x : ℂ)) : ℝ → ℂ) ∘ ((fun y ↦ ⟪y, x⟫_ℝ) : V → ℝ) from ?_] ; swap
        ext y; simp
        exact Continuous.comp continuous_ofReal (Continuous.inner continuous_id' continuous_const)
      exact AEStronglyMeasurable.snd this
      apply AEStronglyMeasurable.mul
      exact AEStronglyMeasurable.fst (Integrable.aestronglyMeasurable hf)
      sorry








/-- Part of **Plancherel theorem**: if `f` is in `L¹ ∩ L²` then its Fourier transform is
also in `L²`. -/
theorem memℒp_fourierIntegral {f : V → ℂ} (hf : Integrable f) (h2f : Memℒp f 2) :
    Memℒp (𝓕 f) 2 := sorry

/-- Part of **Plancherel theorem**: if `f` is in `L¹ ∩ L²` then its inverse Fourier transform is
also in `L²`. -/
theorem memℒp_fourierIntegralInv {f : V → ℂ} (hf : Integrable f) (h2f : Memℒp f 2) :
    Memℒp (𝓕⁻ f) 2 := by
  rw [fourierIntegralInv_eq_fourierIntegral_comp_neg]
  apply memℒp_fourierIntegral (Integrable.comp_neg hf)
  apply Memℒp.comp_of_map
  simp
  exact h2f
  simp_rw [show (fun t ↦ -t) = - (id : V → V) from by ext v; simp]
  exact AEMeasurable.neg aemeasurable_id

def selfConvolution (f : V → ℂ) := convolution f (conj (fun x ↦ f (-x))) (ContinuousLinearMap.mul ℂ ℂ)

lemma integrable_selfConvolution {f : V → ℂ} (hf : Integrable f) : Integrable (selfConvolution f) volume := by
  sorry

lemma fourier_selfConvolution {f : V → ℂ}  (hf : Integrable f) :
    𝓕 (selfConvolution f) = fun x ↦ (‖𝓕 f x‖ : ℂ) ^ 2 := by
  unfold selfConvolution
  rw [fourier_convolution, fourier_conj]
  ext x; simp

  rw [show ((fun x ↦ f (-x)) ∘ fun x ↦ -x) = f from by ext x; simp , mul_conj']
  simp
  exact hf
  apply (integrable_norm_iff ?_).1
  · rw [show (fun a ↦ ‖conj (fun x ↦ f (-x)) a‖) = (fun a ↦ ‖f (-a)‖) from by ext a ; simp]
    exact Integrable.norm (Integrable.comp_neg hf)
  · apply aestronglyMeasurable_iff_aemeasurable.2
    apply Measurable.comp_aemeasurable (Continuous.measurable continuous_conj)
    --simp
    exact Integrable.aemeasurable (Integrable.comp_neg hf)


/-- **Plancherel theorem**: if `f` is in `L¹ ∩ L²` then its Fourier transform has the same
`L²` norm as that of `f`. -/
theorem snorm_fourierIntegral {f : V → ℂ} (hf : Integrable f) (h2f : Memℒp f 2) :
    snorm (𝓕 f) 2 volume = snorm f 2 volume := by
  have lim1 : Tendsto (fun (c : ℝ) ↦ ∫ v : V, cexp (- c⁻¹ * ‖v‖ ^ 2) * 𝓕 (selfConvolution f) v) atTop
      (𝓝 (∫ v : V, ‖f v‖ ^ 2)) := by
    have ha : ∀ c : ℝ , Integrable (fun v : V ↦ cexp (-c⁻¹ * ‖v‖ ^ 2)) volume := by
      sorry

    have : ∀ c : ℝ , ∫ v : V, cexp (-c⁻¹ * ‖v‖ ^ 2) * 𝓕 (selfConvolution f) v = ∫ v : V, 𝓕 (fun w ↦ cexp (c⁻¹ * ‖w‖ ^ 2)) v * (selfConvolution f v) := by
      sorry
      --intro c
      --symm
      --have hc : Continuous ((fun p : V × V ↦ (innerₗ V p.1) p.2)) := by
      --  sorry
      --calc ∫ (v : V), 𝓕 (fun w ↦ cexp (c⁻¹ * ↑‖w‖ ^ 2)) v * selfConvolution f v =
      --  _ = ∫ (w : V), ((ContinuousLinearMap.mul ℂ ℂ) (VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) (fun v ↦ cexp (-c⁻¹ * ↑‖v‖ ^ 2)) w)) (selfConvolution f w) := ?_
      --  _ = ∫ (w : V), (ContinuousLinearMap.mul ℂ ℂ) ((fun v ↦ cexp (-c⁻¹ * ↑‖v‖ ^ 2)) w) (VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) (selfConvolution f) w) :=
      --    VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.mul ℂ ℂ) Real.continuous_fourierChar hc (ha c) (integrable_selfConvolution hf)
      --  _ = ∫ (v : V), cexp (c⁻¹ * ‖v‖ ^ 2) * 𝓕 (slefConvolution f) v := ?_
    sorry




  have lim2 : Tendsto (fun (c : ℝ) ↦ ∫ v : V, cexp (- c⁻¹ * ‖v‖ ^ 2) * 𝓕 (selfConvolution f) v) atTop
      (𝓝 (∫ v : V, ‖𝓕 f v‖ ^ 2)) := by
    rw [fourier_selfConvolution]
    sorry
    sorry

  sorry

example (f g : ℝ → ℂ) (h : f = g) (a : ℂ) (hf : Tendsto f atTop (𝓝 a)) : Tendsto g atTop (𝓝 a) := by
  exact Tendsto.congr (congrFun h) hf

/-- **Plancherel theorem**: if `f` is in `L¹ ∩ L²` then its inverse Fourier transform has the same
`L²` norm as that of `f`. -/
theorem snorm_fourierIntegralInv {f : V → ℂ} (hf : Integrable f) (h2f : Memℒp f 2) :
    snorm (𝓕⁻ f) 2 volume = snorm f 2 volume := by
  trans snorm (𝓕 f) 2 volume
  · unfold snorm; simp; unfold snorm'
    apply congrArg (fun x ↦ x ^ (1 / 2))
    trans ∫⁻ (a : V), ‖𝓕 f (-a)‖₊ ^ (2 : ℝ)
    · apply lintegral_rw₁ _ id
      apply Germ.coe_eq.1 (congrArg Germ.ofFun _)
      ext a
      rw [fourierIntegralInv_eq_fourierIntegral_neg]
    · rw [← @lintegral_map' _ _ _ _ _ (fun x ↦ (‖𝓕 f x‖₊ : ENNReal) ^ 2) (fun x ↦ -x) _ (AEMeasurable.neg aemeasurable_id)]
      simp; simp

      rw [show (fun x ↦ (‖𝓕 f x‖₊ : ENNReal) ^ 2) = (fun x ↦ x ^ 2) ∘ (fun x ↦ (‖𝓕 f x‖₊ : ENNReal)) from by
        ext x; simp]
      apply Measurable.comp_aemeasurable (Measurable.pow_const (fun ⦃t⦄ a ↦ a) 2)

      rw [show (fun x ↦ (‖𝓕 f x‖₊ : ENNReal)) = (fun x ↦ (‖x‖₊ : ENNReal)) ∘ (fun x ↦ 𝓕 f x) from by
        ext x; simp]
      exact Measurable.comp_aemeasurable (Continuous.measurable <| ENNReal.continuous_coe_iff.2 continuous_nnnorm) <|
        AEStronglyMeasurable.aemeasurable (memℒp_fourierIntegral hf h2f).1
  · exact snorm_fourierIntegral hf h2f




scoped[MeasureTheory] notation:25 α " →₁₂[" μ "] " E =>
    ((α →₁[μ] E) ⊓ (α →₂[μ] E) : AddSubgroup (α →ₘ[μ] E))

/- Note: `AddSubgroup.normedAddCommGroup` is almost this, but not quite. -/
instance : NormedAddCommGroup (V →₁₂[volume] E) :=
  AddGroupNorm.toNormedAddCommGroup {
    toFun := fun ⟨f,_⟩ ↦ ENNReal.toReal <| snorm f 2 volume
    map_zero' := by simp [snorm_congr_ae AEEqFun.coeFn_zero, snorm_zero]
    add_le' := fun ⟨f, _, hf⟩ ⟨g, _, hg⟩ ↦ ENNReal.toReal_le_add (by
        simp [snorm_congr_ae (AEEqFun.coeFn_add f g),
              snorm_add_le ((Lp.mem_Lp_iff_memℒp.1 hf).1) ((Lp.mem_Lp_iff_memℒp.1 hg).1)])
      ((Lp.mem_Lp_iff_snorm_lt_top.1 hf).ne) ((Lp.mem_Lp_iff_snorm_lt_top.1 hg).ne)
    neg' := by simp[snorm_congr_ae (AEEqFun.coeFn_neg _)]
    eq_zero_of_map_eq_zero' := by
      intro ⟨f, _, hf⟩ h
      simp [ENNReal.toReal_eq_zero_iff] at h
      rcases h with h | h; swap
      · absurd h; exact (Lp.mem_Lp_iff_snorm_lt_top.1 hf).ne
      ext
      apply ae_eq_trans <| (snorm_eq_zero_iff ((Lp.mem_Lp_iff_memℒp.1 hf).1) (by simp)).1 h
      apply ae_eq_trans (Lp.coeFn_zero E 2 volume).symm; rfl
  }


set_option synthInstance.maxHeartbeats 100000
instance : NormedSpace ℝ (V →₁₂[volume] E) where
  smul := fun a ⟨f, hf⟩ ↦ ⟨a • f, by simp; exact ⟨Lp.const_smul_mem_Lp a ⟨f, hf.1⟩, Lp.const_smul_mem_Lp a ⟨f, hf.2⟩⟩⟩
  one_smul := by
    intro ⟨f, hf⟩
    simp
    sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry
  norm_smul_le := sorry

set_option maxHeartbeats 1000000
/- The Fourier integral as a continuous linear map `L^1(V, E) ∩ L^2(V, E) → L^2(V, E)`. -/
def fourierIntegralL2OfL12Fun : (V →₁₂[volume] E) → (V →₂[volume] E) :=
  fun ⟨f,hf,hf2⟩ ↦ (memℒp_fourierIntegral (memℒp_one_iff_integrable.1 <|
      Lp.mem_Lp_iff_memℒp.1 (by sorry)) (Lp.mem_Lp_iff_memℒp.1 hf2)).toLp <| 𝓕 f

def fourierIntegralL2OfL12 : (V →₁₂[volume] E) →L[ℝ] (V →₂[volume] E) := sorry
  /-have : IsBoundedLinearMap ℝ fourierIntegralL2OfL12Fun := {
    map_add := by
      intro f g
    map_smul := sorry
    bound := sorry
  }
  IsBoundedLinearMap.toContinuousLinearMap this-/



/- The Fourier integral as a continuous linear map `L^2(V, E) → L^2(V, E)`. -/
def fourierIntegralL2 : (V →₂[volume] E) →L[ℝ] (V →₂[volume] E) :=
  sorry

end MeasureTheory
