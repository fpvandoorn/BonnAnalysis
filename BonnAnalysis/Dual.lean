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

lemma symm (hpq : p.IsConjExponent q) : q.IsConjExponent p := ⟨by
    rw [add_comm]
    exact hpq.inv_add_inv_conj⟩

lemma one_le_left (hpq : p.IsConjExponent q) : 1 ≤ p := by
  rw [← ENNReal.inv_le_one, ← hpq.inv_add_inv_conj]
  simp only [self_le_add_right]

lemma one_le_right (hpq : p.IsConjExponent q) : 1 ≤ q := hpq.symm.one_le_left

lemma one_infty : (1 : ℝ≥0∞).IsConjExponent ∞ := ⟨by simp⟩

lemma infty_one : (∞ : ℝ≥0∞).IsConjExponent 1 := ⟨by simp⟩

lemma one_infty' {hp : p = 1} {hq : q = ∞}: p.IsConjExponent q := ⟨by simp [hp, hq]⟩

lemma infty_one' {hp : p = ∞} {hq : q = 1}: p.IsConjExponent q := ⟨by simp [hp, hq]⟩

lemma left_one_iff_right_infty (hpq : p.IsConjExponent q) : p = 1 ↔ q = ∞ := by
  have := hpq.inv_add_inv_conj
  constructor
  intro hp
  rw [← add_zero (1 : ℝ≥0∞), hp, inv_one, AddLECancellable.inj (ENNReal.cancel_of_ne ENNReal.one_ne_top)] at this
  rwa [← ENNReal.inv_eq_zero]
  intro hq
  simp [hq] at this
  assumption

lemma left_infty_iff_right_one (hpq : p.IsConjExponent q) : p = ∞ ↔ q = 1 := (left_one_iff_right_infty hpq.symm).symm

lemma one_lt_left_iff_right_ne_infty (hpq : p.IsConjExponent q) : 1 < p ↔ q ≠ ∞ := by
  rw [← not_iff_not, not_lt, ne_eq, not_not, (left_one_iff_right_infty hpq).symm]
  constructor
  intro hp
  apply LE.le.antisymm hp (one_le_left hpq)
  apply le_of_eq

lemma left_ne_infty_iff_one_lt_right (hpq : p.IsConjExponent q) : p ≠ ∞ ↔ 1 < q := (one_lt_left_iff_right_ne_infty hpq.symm).symm

/- maybe useful: formulate an induction principle. To show something when `p.IsConjExponent q` then it's sufficient to show it in the following cases:
* you have `p q : ℝ≥0` with `p.IsConjExponent q`
* `p = 1` and `q = ∞`
* `p = ∞` and `q = 1` -/

#check ENNReal

lemma coe_is_conj_exponent {p q : ℝ≥0} (hpq : p.IsConjExponent q): (p : ℝ≥0∞).IsConjExponent q where
  inv_add_inv_conj :=  by
   rw [← coe_inv, ← coe_inv, ← coe_add, hpq.inv_add_inv_conj, coe_one]
   apply NNReal.IsConjExponent.ne_zero hpq.symm
   apply NNReal.IsConjExponent.ne_zero hpq

lemma toNNReal_is_conj_exponent {p q : ℝ≥0∞} (hp : 1 < p) (hq : 1 < q) (hpq : p.IsConjExponent q): (p.toNNReal).IsConjExponent (q.toNNReal) where
  one_lt := by
    rwa [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal ((left_ne_infty_iff_one_lt_right hpq).mpr hq)]
  inv_add_inv_conj := by
    rw [← ENNReal.coe_inj, coe_add, coe_inv, coe_inv]
    convert hpq.inv_add_inv_conj
    rw [ENNReal.coe_toNNReal ((left_ne_infty_iff_one_lt_right hpq).mpr hq)]
    rw [ENNReal.coe_toNNReal ((one_lt_left_iff_right_ne_infty hpq).mp hp)]
    exact (ENNReal.toNNReal_ne_zero).mpr ⟨(zero_lt_one.trans hq).ne', ((one_lt_left_iff_right_ne_infty hpq).mp hp)⟩
    exact (ENNReal.toNNReal_ne_zero).mpr ⟨(zero_lt_one.trans hp).ne', ((left_ne_infty_iff_one_lt_right hpq).mpr hq)⟩

lemma induction
  (f : (p: ENNReal) → (q :ENNReal) → (p.IsConjExponent q) → Prop)
  (h₁ : ∀  p q : ℝ≥0, (h : p.IsConjExponent q) → f p q (coe_is_conj_exponent h))
  (h₂ : f 1 ∞ one_infty)
  (h₃ : f ∞ 1 infty_one) :
  ∀ p q : ℝ≥0∞, (h : p.IsConjExponent q) → f p q h := by
  intro p q h
  by_cases hq : q = ∞
  have hp : p = 1 := (left_one_iff_right_infty h).mpr hq
  simp_rw [hp, hq]
  exact h₂
  by_cases hp : p = ∞
  have hq₂ : q = 1 := (left_infty_iff_right_one h).mp hp
  simp_rw [hp, hq₂]
  exact h₃
  have := h₁ p.toNNReal q.toNNReal <| toNNReal_is_conj_exponent ((one_lt_left_iff_right_ne_infty h).mpr hq) ((left_ne_infty_iff_one_lt_right h).mp hp) h
  simp_rw [ENNReal.coe_toNNReal hp, ENNReal.coe_toNNReal hq] at this
  exact this

/- add various other needed lemmas below (maybe look at `NNReal.IsConjExponent` for guidance) -/

/- Versions of Hölder's inequality.
Note that the hard case already exists as `ENNReal.lintegral_mul_le_Lp_mul_Lq`. -/
#check ENNReal.lintegral_mul_le_Lp_mul_Lq
#check ContinuousLinearMap.le_opNorm

lemma bilin_le_opNorm  {L : E₁ →L[𝕜] E₂ →L[𝕜] E₃} {f : α → E₁} {g : α → E₂} (a : α) : ‖L (f a) (g a)‖ ≤ ‖L‖ * ‖f a‖ * ‖g a‖ := by
  apply LE.le.trans (ContinuousLinearMap.le_opNorm (L (f a)) (g a))
  apply mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm L (f a)) (norm_nonneg (g a))

lemma bilin_le_opNorm_nnreal {L : E₁ →L[𝕜] E₂ →L[𝕜] E₃} {f : α → E₁} {g : α → E₂} (a : α) : ‖L (f a) (g a)‖₊ ≤ ‖L‖₊ * (‖f a‖₊ * ‖g a‖₊) := by
  rw [← mul_assoc, ← NNReal.coe_le_coe]
  simp only [coe_nnnorm, NNReal.coe_mul]
  apply bilin_le_opNorm

lemma lintegral_mul_le_one_infty (μ : Measure α) {f : α → E₁} {g : α → E₂}
    (hf : AEMeasurable f μ) : ∫⁻ a, ‖f a‖₊ * ‖g a‖₊ ∂μ ≤ snorm f 1 μ * snorm g ⊤ μ := by
    calc ∫⁻ a, ‖f a‖₊ * ‖g a‖₊ ∂μ ≤ ∫⁻ (a : α), ‖f a‖₊ * snormEssSup g μ ∂μ := MeasureTheory.lintegral_mono_ae (h := by
        rw [Filter.eventually_iff, ← Filter.exists_mem_subset_iff]
        use {a | ↑‖g a‖₊ ≤ snormEssSup g μ}
        rw [← Filter.eventually_iff]
        exact ⟨ae_le_snormEssSup, by simp; intro _ ha; apply ENNReal.mul_left_mono ha⟩)
    _ = snorm f 1 μ * snorm g ⊤ μ := by
      rw [lintegral_mul_const'']
      simp [snorm, snorm']
      exact Measurable.comp_aemeasurable' measurable_coe_nnreal_ennreal (Measurable.comp_aemeasurable' measurable_nnnorm hf)

theorem lintegral_mul_le (hpq : p.IsConjExponent q) (μ : Measure α) {f : α → E₁} {g : α → E₂}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, ‖L (f a) (g a)‖₊ ∂μ ≤ ‖L‖₊ * snorm f p μ * snorm g q μ := by
  induction p, q, hpq using IsConjExponent.induction
  case h₁ p q hpq =>
    calc ∫⁻ a, ‖L (f a) (g a)‖₊ ∂μ ≤ ∫⁻ a, ‖L‖₊ * (‖f a‖₊ * ‖g a‖₊) ∂μ :=
      lintegral_mono_nnreal bilin_le_opNorm_nnreal
    _ = ‖L‖₊ * ∫⁻ a, ‖f a‖₊ * ‖g a‖₊ ∂μ := lintegral_const_mul' _ _ coe_ne_top
    _ = ‖L‖₊ * ∫⁻ a, ((fun a ↦ ‖f a‖₊) * (fun a ↦ ‖g a‖₊)) a ∂μ := by
      apply congrArg (HMul.hMul _)
      apply lintegral_congr
      simp only [Pi.mul_apply, coe_mul, implies_true]
    _ ≤ ‖L‖₊ * snorm f p μ * snorm g q μ := by
      rw [mul_assoc]
      by_cases hL : ‖L‖₊ = 0
      simp [hL]
      apply (ENNReal.mul_le_mul_left _ coe_ne_top).mpr
      simp only [coe_mul, snorm, coe_eq_zero, coe_ne_top, ↓reduceIte, coe_toReal, mul_ite, mul_zero, ite_mul, zero_mul, NNReal.IsConjExponent.ne_zero hpq, NNReal.IsConjExponent.ne_zero hpq.symm, snorm']
      apply ENNReal.lintegral_mul_le_Lp_mul_Lq
      apply NNReal.isConjExponent_coe.mpr hpq
      . apply Measurable.comp_aemeasurable' measurable_coe_nnreal_ennreal (Measurable.comp_aemeasurable' measurable_nnnorm hf)
      . apply Measurable.comp_aemeasurable' measurable_coe_nnreal_ennreal (Measurable.comp_aemeasurable' measurable_nnnorm hg)
      simpa [ne_eq, coe_zero]
  case h₂ =>
    calc ∫⁻ a, ‖L (f a) (g a)‖₊ ∂μ ≤ ∫⁻ a, ‖L‖₊ * (‖f a‖₊ * ‖g a‖₊) ∂μ :=
      lintegral_mono_nnreal bilin_le_opNorm_nnreal
    _ = ‖L‖₊ * ∫⁻ a, ‖f a‖₊ * ‖g a‖₊ ∂μ := lintegral_const_mul' _ _ coe_ne_top
    _ ≤ ‖L‖₊ * snorm f 1 μ * snorm g ⊤ μ := by
      rw [mul_assoc]
      apply ENNReal.mul_left_mono
      apply lintegral_mul_le_one_infty
      exact hf
  case h₃ =>
    calc ∫⁻ a, ‖L (f a) (g a)‖₊ ∂μ ≤ ∫⁻ a, ‖L‖₊ * (‖f a‖₊ * ‖g a‖₊) ∂μ :=
      lintegral_mono_nnreal bilin_le_opNorm_nnreal
    _ = ‖L‖₊ * ∫⁻ a, ‖f a‖₊ * ‖g a‖₊ ∂μ := lintegral_const_mul' _ _ coe_ne_top
    _ = ‖L‖₊ * ∫⁻ a, ‖g a‖₊ * ‖f a‖₊ ∂μ := by simp_rw [mul_comm]
    _ ≤ ‖L‖₊ * snorm f ⊤ μ * snorm g 1 μ := by
      rw [mul_assoc, mul_comm (snorm f ⊤ μ)]
      apply ENNReal.mul_left_mono
      apply lintegral_mul_le_one_infty
      exact hg

-- (hpq : p.IsConjExponent q) is missing
theorem integrable_bilin (hpq : p.IsConjExponent q) (μ : Measure α) {f : α → E₁} {g : α → E₂}
    (hf : Memℒp f p μ) (hg : Memℒp g q μ) :
    Integrable (fun a ↦ L (f a) (g a)) μ := by
      dsimp [Integrable]
      constructor
      . apply ContinuousLinearMap.aestronglyMeasurable_comp₂
        apply (MeasureTheory.Memℒp.aestronglyMeasurable hf)
        apply (MeasureTheory.Memℒp.aestronglyMeasurable hg)
      . dsimp [HasFiniteIntegral]
        apply lt_of_le_of_lt <| lintegral_mul_le L hpq μ (MeasureTheory.AEStronglyMeasurable.aemeasurable (MeasureTheory.Memℒp.aestronglyMeasurable hf)) (MeasureTheory.AEStronglyMeasurable.aemeasurable (MeasureTheory.Memℒp.aestronglyMeasurable hg))
        apply ENNReal.mul_lt_top (ENNReal.mul_ne_top coe_ne_top (MeasureTheory.Memℒp.snorm_ne_top hf)) (MeasureTheory.Memℒp.snorm_ne_top hg)

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
def dualIsometry (L : E₁ ≃L[𝕜] Dual 𝕜 E₂) :
    Dual 𝕜 (Lp E₂ p μ) ≃ₗᵢ[𝕜] Lp E q μ :=
  sorry

end Lp
end MeasureTheory
