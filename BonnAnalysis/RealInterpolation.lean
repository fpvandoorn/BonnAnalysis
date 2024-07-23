import BonnAnalysis.LorentzSpace

noncomputable section

open NNReal ENNReal NormedSpace MeasureTheory Set

variable {α β E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {n : MeasurableSpace β} {p q : ℝ≥0∞}
  {μ : Measure α} {ν : Measure β}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [FiniteDimensional ℝ E₃]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E₁] [BorelSpace E₁]
  [MeasurableSpace E₂] [BorelSpace E₂]
  [MeasurableSpace E₃] [BorelSpace E₃]
  {f : α → E} {t : ℝ}

namespace MeasureTheory

/-- The `t`-truncation of a function `f`. -/
def trunc (f : α → E) (t : ℝ) (x : α) : E := if ‖f x‖ ≤ t then f x else 0

lemma aestronglyMeasurable_trunc (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (trunc f t) μ := sorry

/-- The `t`-truncation of `f : α →ₘ[μ] E`. -/
def AEEqFun.trunc (f : α →ₘ[μ] E) (t : ℝ) : α →ₘ[μ] E :=
  AEEqFun.mk (MeasureTheory.trunc f t) (aestronglyMeasurable_trunc f.aestronglyMeasurable)

/-- A set of measurable functions is closed under truncation. -/
class IsClosedUnderTruncation (U : Set (α →ₘ[μ] E)) : Prop where
  trunc_mem {f : α →ₘ[μ] E} (hf : f ∈ U) (t : ℝ) : f.trunc t ∈ U

def Subadditive (T : (α →ₘ[μ] E₁) → β →ₘ[ν] E₂) : Prop :=
  ∃ A > 0, ∀ (f g : α →ₘ[μ] E₁), ∀ᵐ x ∂ν, ‖T (f + g) x‖ ≤ A * (‖T f x‖ + ‖T g x‖)

def LBounded (T : (α →ₘ[μ] E₁) → β →ₘ[ν] E₂) (p r s : ℝ≥0∞) : Prop :=
  ∃ C > 0, ∀ (f : α →ₘ[μ] E₁), lnorm f p s μ < ∞ → lnorm (T f) r ∞ ν ≤ C * lnorm f p s μ

-- /- An alternate definition is the following, but I think it will be harder to work with: -/
-- def subadditive' (T : (α →ₘ[μ] E) → β →ₘ[ν] E) : Prop :=
--   ∃ A > 0, ∀ (f g : α →ₘ[μ] E), (T (f + g)).comp norm continuous_norm ≤
--     (A : ℝ) • ((T f).comp norm continuous_norm + (T g).comp norm continuous_norm)

/- to do: state and proof lemmas towards the theorem below. -/

/-- Marcinkiewicz real interpolation theorem. -/
theorem exists_lnorm_le_of_subadditive_of_lbounded {p₀ p₁ r₀ r₁ s₀ s₁ : ℝ≥0∞}
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hp : p₀ < p₁)
    (hr₀ : 1 ≤ r₀) (hr₁ : 1 ≤ r₁) (hr : r₀ ≠ r₁)
    (hs₀ : s₀ = 1) (hs₁ : s₁ = if p₁ < ∞ then 1 else ∞)
    (U : Submodule ℝ (α →ₘ[μ] E₁)) [IsClosedUnderTruncation (U : Set (α →ₘ[μ] E₁))]
    (T : (α →ₘ[μ] E₁) → β →ₘ[ν] E₂) (hT : Subadditive T)
    (h₀T : LBounded T p₀ r₀ 1) (h₁T : LBounded T p₁ r₁ s₁)
    {θ : ℝ≥0} (hθ : θ ∈ Ioo 0 1) :
    ∃ C > 0, ∀ (p q r : ℝ≥0∞) (hp : p⁻¹ = (1 - θ) / p₀ + θ / p₁) (hr : r⁻¹ = (1 - θ) / r₀ + θ / r₁),
      ∀ (f : α →ₘ[μ] E₁), f ∈ U → lnorm f p s₀ μ < ∞ → lnorm (T f) r q ν ≤ C * lnorm f p q μ := sorry

/- State and prove Remark 1.2.7 -/

end MeasureTheory
