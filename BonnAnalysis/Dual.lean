import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Analysis.NormedSpace.LinearIsometry

/-! We show that the dual space of `L^p` for `1 ≤ p < ∞`.

See [Stein-Shakarchi, Functional Analysis, section 1.4] -/
noncomputable section

open Real NNReal ENNReal NormedSpace MeasureTheory

variable {α 𝕜 E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {p q : ℝ≥0∞}
  {μ : Measure α} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃] [FiniteDimensional 𝕜 E₃]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E₁] [BorelSpace E₁]
  [MeasurableSpace E₂] [BorelSpace E₂]
  [MeasurableSpace E₃] [BorelSpace E₃]
  (L : E₁ →L[𝕜] E₂ →L[𝕜] E₃)

namespace ENNReal

/-- Two numbers `p, q : ℝ≥0∞` are conjugate if `p⁻¹ + q⁻¹ = 1`.
This does allow for the case where one of them is `∞` and the other one is `1`,
in contrast to `NNReal.IsConjExponent`. -/
structure IsConjExponent (p q : ℝ≥0∞) : Prop where
  inv_add_inv_conj : p⁻¹ + q⁻¹ = 1

namespace IsConjExponent

lemma one_le_left (hpq : p.IsConjExponent q) : 1 ≤ p := sorry

lemma symm (hpq : p.IsConjExponent q) : q.IsConjExponent p where
  inv_add_inv_conj := by
    rw [add_comm]
    exact hpq.inv_add_inv_conj


lemma one_le_right (hpq : p.IsConjExponent q) : 1 ≤ q := hpq.symm.one_le_left

/- maybe useful: formulate an induction principle. To show something when `p.IsConjExponent q` then it's sufficient to show it in the following cases:
* you have `p q : ℝ≥0` with `p.IsConjExponent q`
* `p = 1` and `q = ∞`
* `p = ∞` and `q = 1` -/


/- add various other needed lemmas below (maybe look at `NNReal.IsConjExponent` for guidance) -/


/- Versions of Hölder's inequality.
Note that the hard case already exists as `ENNReal.lintegral_mul_le_Lp_mul_Lq`. -/
#check ENNReal.lintegral_mul_le_Lp_mul_Lq
#check ContinuousLinearMap.le_opNorm

theorem lintegral_mul_le (μ : Measure α) {f : α → E₁} {g : α → E₂}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, ‖L (f a) (g a)‖₊ ∂μ ≤ ‖L‖₊ * snorm f p μ * snorm g q μ := by
  sorry

theorem integrable_bilin (μ : Measure α) {f : α → E₁} {g : α → E₂}
    (hf : Memℒp f p μ) (hg : Memℒp g q μ) :
    Integrable (fun a ↦ L (f a) (g a)) μ := by sorry

end IsConjExponent
end ENNReal


namespace MeasureTheory
namespace Lp
-- note: we may need to restrict to `𝕜 = ℝ`
variable
  [hpq : Fact (p.IsConjExponent q)] [h'p : Fact (p < ∞)]
  [hp : Fact (1 ≤ p)] [hq : Fact (1 ≤ q)] -- note: these are superfluous, but it's tricky to make them instances.

/- The map sending `g` to `f ↦ ∫ x, L (f x) (g x) ∂μ` induces a map on `L^p` into
`Lp E₂ p μ →L[𝕜] E₃`. Generally we will take `E₃ = 𝕜`. -/
variable (p μ) in
def toDual (g : Lp E₁ q μ) : Lp E₂ p μ →L[𝕜] E₃ :=
  sorry

/- The map sending `g` to `f ↦ ∫ x, L (f x) (g x) ∂μ` is a linear isometry. -/
variable (p q μ) in
def toDualₗᵢ : Lp E₁ q μ →ₗᵢ[𝕜] Lp E₂ p μ →L[𝕜] E₃ :=
  sorry

/- The map sending `g` to `f ↦ ∫ x, L (f x) (g x) ∂μ` is a linear isometric equivalence.  -/
variable (p q μ) in
def dualIsometry (L : E₁ →L[𝕜] Dual 𝕜 E₂) :
    Dual 𝕜 (Lp E₂ p μ) ≃ₗᵢ[𝕜] Lp E q μ :=
  sorry

end Lp
end MeasureTheory
