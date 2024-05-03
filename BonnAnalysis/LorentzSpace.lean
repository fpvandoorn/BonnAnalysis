import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Analysis.NormedSpace.LinearIsometry

noncomputable section

open NNReal ENNReal NormedSpace MeasureTheory Set Filter Topology

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
  {f g : α → E} {t s x y : ℝ≥0∞}

#check meas_ge_le_mul_pow_snorm -- Chebyshev's inequality

namespace MeasureTheory
/- If we need more properties of `E`, we can add `[RCLike E]` *instead of* the above type-classes-/
#check _root_.RCLike

/-! # The distribution function `d_f` -/

/-- The distribution function `d_f` of a function `f`.
Note that unlike the notes, we also define this for `t = ∞`.
Note: we also want to use this for functions with codomain `ℝ≥0∞`, but for those we just write
`μ { x | t < f x }` -/
def distribution [NNNorm E] (f : α → E) (t : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  μ { x | t < ‖f x‖₊ }

@[gcongr] lemma distribution_mono_left (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    distribution f t μ ≤ distribution g t μ := sorry

@[gcongr] lemma distribution_mono_right (h : t ≤ s) :
    distribution f s μ ≤ distribution f t μ := sorry

@[gcongr] lemma distribution_mono (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) (h : t ≤ s) :
    distribution f s μ ≤ distribution g t μ := sorry

lemma distribution_smul_left {c : 𝕜} (hc : c ≠ 0) :
    distribution (c • f) t μ = distribution f (t / ‖c‖₊) μ := sorry

lemma distribution_add_le :
    distribution (f + g) (t + s) μ ≤ distribution f t μ + distribution g s μ := sorry

lemma _root_.ContinuousLinearMap.distribution_le {f : α → E₁} {g : α → E₂} :
    distribution (fun x ↦ L (f x) (g x)) (‖L‖₊ * t * s) μ ≤
    distribution f t μ + distribution g s μ := sorry


/- The layer-cake theorem already exists -/
#check MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul

lemma lintegral_norm_pow {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, ‖f x‖₊ ^ p ∂μ =
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (p * t ^ (p - 1)) * distribution f (.ofReal t) μ  := sorry


/-! # Decreasing rearrangements `f^#` -/

/-- The decreasing rearrangement function `f^#`. It equals `μ univ` for negative `x`.
Note that unlike the notes, we also define this for `x = ∞`.
To do: we should also be able to  use this for functions with codomain `ℝ≥0∞`. -/
def rearrangement [NNNorm E] (f : α → E) (x : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  sInf {s : ℝ≥0∞ | distribution f s μ ≤ x }

/- to do: state and prove lemmas about `f^#`. -/

@[gcongr] lemma rearrangement_mono_right (h : x ≤ y) :
    rearrangement f y μ ≤ rearrangement f x μ := sorry

@[gcongr] lemma rearrangement_mono_left (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    rearrangement f x μ ≤ rearrangement g x μ := sorry

@[gcongr] lemma rearrangement_mono (h1 : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) (h2 : x ≤ y) :
    rearrangement f y μ ≤ rearrangement g x μ := sorry

lemma rearrangement_smul_left (c : 𝕜) :
    rearrangement (c • f) x μ = ‖c‖₊ * rearrangement f x μ := sorry

-- this should also hold if `distribution f t μ = ∞`.
lemma rearrangement_distribution_le : rearrangement f (distribution f t μ) μ ≤ t := sorry

-- this should also hold if `rearrangement f x μ = ∞`.
lemma distribution_rearrangement_le : distribution f (rearrangement f x μ) μ ≤ x := sorry

lemma rearrangement_add_le (c : 𝕜) :
    rearrangement (f + g) (x + y) μ ≤ rearrangement f x μ + rearrangement g y μ := sorry

lemma _root_.ContinuousLinearMap.rearrangement_le {f : α → E₁} {g : α → E₂} :
    rearrangement (fun x ↦ L (f x) (g x)) (‖L‖₊ * x * y) μ ≤
    rearrangement f x μ + rearrangement g y μ := sorry

-- Lemma 1.1.22 of [Ian Tice]
lemma lt_rearrangement_iff (hf : Measurable f) :
    s < rearrangement f x μ ↔ x < distribution f s μ := sorry

-- Lemma 1.1.22 of [Ian Tice]
lemma continuousWithinAt_rearrangement (hf : Measurable f) (x : ℝ≥0∞) :
    ContinuousWithinAt (rearrangement f · μ) (Ici x) x := sorry

-- Lemma 1.1.22 of [Ian Tice]
lemma volume_lt_rearrangement (hf : Measurable f) (s : ℝ≥0∞) :
    volume { x | s < rearrangement f (.ofReal x) μ } = distribution f s μ := sorry

-- Lemma 1.1.22 of [Ian Tice]
lemma lintegral_rearrangement_pow (hf : Measurable f) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ t, (rearrangement f (.ofReal t) μ) ^ p = ∫⁻ x, ‖f x‖₊ ∂μ := sorry

-- Lemma 1.1.22 of [Ian Tice]
lemma sSup_rearrangement (hf : Measurable f) :
    ⨆ t > 0, rearrangement f t μ = rearrangement f 0 μ := sorry

-- Lemma 1.1.22 of [Ian Tice]
lemma essSup_nnnorm_eq_rearrangement_zero (hf : Measurable f) :
    essSup (‖f ·‖₊) μ = rearrangement f 0 μ  := sorry

-- Lemma 1.1.23 of [Ian Tice]
lemma tendsto_rearrangement {s : ℕ → α → E} (hs : ∀ᶠ i in atTop, Measurable (s i))
    (hf : Measurable f) (h2s : ∀ᵐ x ∂μ, Monotone (fun n ↦ ‖s n x‖))
    (h : ∀ᵐ x ∂μ, Tendsto (‖s · x‖) atTop (𝓝 ‖f x‖)) :
    Tendsto s atTop (𝓝 f) := sorry

-- Lemma 1.1.23 of [Ian Tice]
lemma liminf_rearrangement {s : ℕ → α → E} (hs : ∀ᶠ i in atTop, Measurable (s i))
    (hf : Measurable f) (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ liminf (‖s · x‖) atTop) :
    rearrangement f x μ ≤ liminf (fun i ↦ rearrangement (s i) x μ) atTop := sorry

-- Lemma 1.1.24 of [Ian Tice]
lemma distribution_indicator_le_distribution {f : α → E} (hf : Measurable f)
    {X : Set α} (hX : MeasurableSet X) (t : ℝ≥0∞) (μ : Measure α) :
    distribution (X.indicator f) t μ ≤ distribution f t μ := sorry

-- Lemma 1.1.24 of [Ian Tice]
lemma distribution_indicator_le_measure {f : α → E} (hf : Measurable f)
    {X : Set α} (hX : MeasurableSet X) (t : ℝ≥0∞) (μ : Measure α) :
    distribution (X.indicator f) t μ ≤ μ X := sorry

/- The interval `[0, a) ⊆ ℝ` for `a : ℝ≥0∞`, if useful. -/
protected def _root_.ENNReal.Ico (a : ℝ≥0∞) : Set ℝ :=
  {x : ℝ | 0 ≤ x ∧ ENNReal.ofReal x < a}

/- to do: some computation rules for this set. -/

/-- Version of `rearrangement_indicator_le` for `t : ℝ≥0∞` -/
lemma rearrangement_indicator_le' {f : α → E} (hf : Measurable f)
    {X : Set α} (hX : MeasurableSet X) (t : ℝ≥0∞) (μ : Measure α) :
    rearrangement (X.indicator f) t μ ≤
    indicator (Iio (μ X)) (rearrangement f · μ) t := sorry

-- Lemma 1.1.24 of [Ian Tice]
lemma rearrangement_indicator_le {f : α → E} (hf : Measurable f)
    {X : Set α} (hX : MeasurableSet X) (t : ℝ) (μ : Measure α) :
    rearrangement (X.indicator f) (.ofReal t) μ ≤
    indicator (μ X).Ico (fun x ↦ rearrangement f (.ofReal x) μ) t := sorry

-- Lemma 1.1.24 of [Ian Tice]
lemma integral_norm_le_integral_rearrangement {f : α → E} (hf : Measurable f)
    {X : Set α} (hX : MeasurableSet X) (μ : Measure α) :
    ∫⁻ x, ‖f x‖₊ ∂μ ≤
    ∫⁻ t in (μ X).Ico, rearrangement f (ENNReal.ofReal t) μ := sorry

-- todo: Hardy-Littlewood rearrangement inequality for functions into `ℝ≥0∞`.

/-- The Hardy-Littlewood rearrangement inequality, for functions into `𝕜` -/
theorem lintegral_norm_mul_le_lintegral_rearrangement_mul {f g : α → 𝕜} :
    ∫⁻ x, ‖f x * g x‖₊ ∂μ ≤
    ∫⁻ t, rearrangement f (.ofReal t) μ * rearrangement g (.ofReal t) μ := by
  sorry

/-- The norm corresponding to the Lorentz space `L^{p,q}` for `1 ≤ p ≤ ∞` and `1 ≤ q < ∞`. -/
def lnorm' (f : α → E) (p : ℝ≥0∞) (q : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  ∫⁻ t : ℝ, (ENNReal.ofReal (t ^ (p⁻¹).toReal) *
  rearrangement f (.ofReal t) μ) ^ q⁻¹ / (ENNReal.ofReal t)

/- to do: state and prove lemmas about `lnorm'`. -/

/-- The norm corresponding to the Lorentz space `L^{p,q}` for `1 ≤ p ≤ ∞` and `1 ≤ q ≤ ∞`. -/
def lnorm (f : α → E) (p q : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if q = ∞ then
    ⨆ t > 0, ENNReal.ofReal (t ^ (p⁻¹).toReal) * rearrangement f (.ofReal t) μ
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
