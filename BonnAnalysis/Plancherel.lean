import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

noncomputable section

open FourierTransform MeasureTheory Real

namespace MeasureTheory

/- The Fourier transform and it's inverse. -/
#check fourierIntegral -- notation: `𝓕`
#check fourierIntegralInv -- notation: `𝓕⁻`

/- Other important concepts -/
#check snorm
#check Memℒp
#check Lp

/- The Fourier coefficients for a periodic function. -/
#check fourierCoeff

/- Potentially useful lemmas -/
#check VectorFourier.norm_fourierIntegral_le_integral_norm
#check VectorFourier.integral_fourierIntegral_smul_eq_flip

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V]

/-- Part of **Plancherel theorem**: if `f` is in `L¹ ∩ L²` then its Fourier transform is also in
`L²`. -/
theorem memℒp_fourierIntegral {f : V → E} (hf : Integrable f) (h2f : Memℒp f 2) :
    Memℒp (𝓕 f) 2 := sorry

/-- Part of **Plancherel theorem**: if `f` is in `L¹ ∩ L²` then its inverse Fourier transform is
also in `L²`. -/
theorem memℒp_fourierIntegralInv {f : V → E} (hf : Integrable f) (h2f : Memℒp f 2) :
    Memℒp (𝓕⁻ f) 2 := sorry

/-- **Plancherel theorem**: if `f` is in `L¹ ∩ L²` then its Fourier transform has the same
`L²` norm as that of `f`. -/
theorem snorm_fourierIntegral {f : V → E} (hf : Integrable f) (h2f : Memℒp f 2) :
    snorm (𝓕 f) 2 volume = snorm f 2 volume := sorry

/-- **Plancherel theorem**: if `f` is in `L¹ ∩ L²` then its inverse Fourier transform has the same
`L²` norm as that of `f`. -/
theorem snorm_fourierIntegralInv {f : V → E} (hf : Integrable f) (h2f : Memℒp f 2) :
    snorm (𝓕⁻ f) 2 volume = snorm f 2 volume := sorry


scoped[MeasureTheory] notation:25 α " →₁₂[" μ "] " E =>
    ((α →₁[μ] E) ⊓ (α →₂[μ] E) : AddSubgroup (α →ₘ[μ] E))


/- Note: `AddSubgroup.normedAddCommGroup` is almost this, but not quite. -/
instance : NormedAddCommGroup (V →₁₂[volume] E) :=
  AddGroupNorm.toNormedAddCommGroup sorry
instance : NormedSpace ℝ (V →₁₂[volume] E) := sorry


/- The Fourier integral as a continuous linear map `L^1(V, E) ∩ L^2(V, E) → L^2(V, E)`. -/
def fourierIntegralL2OfL12 : (V →₁₂[volume] E) →L[ℝ] (V →₂[volume] E) :=
    sorry


/- The Fourier integral as a continuous linear map `L^2(V, E) → L^2(V, E)`. -/
def fourierIntegralL2 : (V →₂[volume] E) →L[ℝ] (V →₂[volume] E) :=
  sorry

end MeasureTheory
