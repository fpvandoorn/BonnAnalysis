import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Analysis.NormedSpace.LinearIsometry

noncomputable section

open NNReal ENNReal NormedSpace MeasureTheory Set

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

#check meas_ge_le_mul_pow_snorm -- Chebyshev's inequality

namespace MeasureTheory
/- If we need more properties of `E`, we can add `[RCLike E]` *instead of* the above type-classes-/
#check _root_.RCLike

/-- The distribution function `d_f` of a function `f`. -/
def distribution [NNNorm E] (f : α → E) (y : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  μ { x | y < ‖f x‖₊ }

/- to do: state and prove lemmas about `d_f`. -/

/-- The decreasing rearrangement function `f^#`. It equals `μ univ` for negative `x`. -/
def rearrangement [NNNorm E] (f : α → E) (x : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  sInf {s : ℝ≥0∞ | distribution f s μ ≤ ENNReal.ofReal x }

/- to do: state and prove lemmas about `f^#`. -/

-- Part of Lemma 1.1.24 of [Ian Tice]
lemma distribution_indicator_le_distribution {f : α → E} (hf : Measurable f)
    {X : Set α} (hX : MeasurableSet X) (t : ℝ≥0∞) (μ : Measure α) :
    distribution (X.indicator f) t μ ≤ distribution f t μ := sorry

-- Part of Lemma 1.1.24 of [Ian Tice]
lemma distribution_indicator_le_measure {f : α → E} (hf : Measurable f)
    {X : Set α} (hX : MeasurableSet X) (t : ℝ≥0∞) (μ : Measure α) :
    distribution (X.indicator f) t μ ≤ μ X := sorry

/- The interval `[0, a) ⊆ ℝ` for `a : ℝ≥0∞` -/
protected def _root_.ENNReal.Ico (a : ℝ≥0∞) : Set ℝ :=
  {x : ℝ | 0 ≤ x ∧ ENNReal.ofReal x < a}

/- to do: some computation rules for this set. -/

/-- The Hardy-Littlewood rearrangement inequality -/
lemma rearrangement_indicator_le {f : α → E} (hf : Measurable f)
    {X : Set α} (hX : MeasurableSet X) {t : ℝ} (ht : 0 ≤ t) (μ : Measure α) :
    rearrangement (X.indicator f) t μ ≤
    indicator (μ X).Ico (rearrangement f · μ) t := sorry

/-- The Hardy-Littlewood rearrangement inequality -/
lemma integral_norm_le_integral_rearrangement {f : α → E} (hf : Measurable f)
    {X : Set α} (hX : MeasurableSet X) (μ : Measure α) :
    ∫⁻ x, ‖f x‖₊ ∂μ ≤
    ∫⁻ t : ℝ in (μ X).Ico, rearrangement f t μ := sorry

/-- The norm corresponding to the Lorentz space `L^{p,q}` for `1 ≤ p ≤ ∞` and `1 ≤ q < ∞`. -/
def lnorm' (f : α → E) (p : ℝ≥0∞) (q : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  ∫⁻ t : ℝ, (ENNReal.ofReal (t ^ (p⁻¹).toReal) * rearrangement f t μ) ^ q⁻¹ / (ENNReal.ofReal t)

/- to do: state and prove lemmas about `lnorm'`. -/

/-- The norm corresponding to the Lorentz space `L^{p,q}` for `1 ≤ p ≤ ∞` and `1 ≤ q ≤ ∞`. -/
def lnorm (f : α → E) (p q : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if q = ∞ then
    ⨆ t > 0, ENNReal.ofReal (t ^ (p⁻¹).toReal) * rearrangement f t μ
  else
    lnorm' f p q.toReal μ

/- to do: double check definition for `p = ∞`
to do: state and prove lemmas about `lnorm`. -/

/-- the Lorentz space `L^{p,q}` -/
def Lorentz {α} (E : Type*) {m : MeasurableSpace α} [NormedAddCommGroup E] (p q : ℝ≥0∞)
    (μ : Measure α := by volume_tac) : AddSubgroup (α →ₘ[μ] E) where
  carrier := { f | lnorm f p q μ < ∞ }
  zero_mem' := by sorry
  add_mem' {f g} hf hg := by sorry
  neg_mem' {f} hf := by sorry


end MeasureTheory
