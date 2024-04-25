import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-! Some useful definitions and theorems for this project. -/

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

#check lintegral
#check integral


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V]

-- you can apply an `L^p` function to an argument, even if it is really an equivalence class of functions. It takes an arbitrary representative
example (f : Lp E 1 (volume : Measure V)) (x : V) : f x = f x := by rfl
-- that means that the following is not provable, since the representative is not guaranteed to be the same as the function you started with.
example (f : V → E) (hf : Memℒp f 1) (x : V) :
  (hf.toLp f) x = f x := by sorry -- unprovable
