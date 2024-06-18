import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Analysis.NormedSpace.LinearIsometry
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Data.Real.Sign
import Mathlib.Tactic.FunProp.Measurable

/-! We show that the dual space of `L^p` for `1 ≤ p < ∞`.

See [Stein-Shakarchi, Functional Analysis, section 1.4] -/
noncomputable section

open Real NNReal ENNReal NormedSpace MeasureTheory
section

variable {α 𝕜 E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {p p' q q' : ℝ≥0∞}
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
@[mk_iff]
structure IsConjExponent (p q : ℝ≥0∞) : Prop where
  inv_add_inv_conj : p⁻¹ + q⁻¹ = 1

namespace IsConjExponent

lemma symm (hpq : p.IsConjExponent q) : q.IsConjExponent p := by
    rw [isConjExponent_iff, add_comm, hpq.inv_add_inv_conj]

lemma one_le_left (hpq : p.IsConjExponent q) : 1 ≤ p := by
  simp_rw [← ENNReal.inv_le_one, ← hpq.inv_add_inv_conj, self_le_add_right]

lemma one_le_right (hpq : p.IsConjExponent q) : 1 ≤ q := hpq.symm.one_le_left

lemma left_ne_zero (hpq : p.IsConjExponent q) : p ≠ 0 :=
  zero_lt_one.trans_le hpq.one_le_left |>.ne'

lemma right_ne_zero (hpq : p.IsConjExponent q) : q ≠ 0 :=
  hpq.symm.left_ne_zero

lemma left_inv_ne_top (hpq : p.IsConjExponent q) : p⁻¹ ≠ ∞ := by
  simp_rw [inv_ne_top]
  exact hpq.left_ne_zero

lemma right_inv_ne_top (hpq : p.IsConjExponent q) : q⁻¹ ≠ ∞ := hpq.symm.left_inv_ne_top

lemma left_eq (hpq : p.IsConjExponent q) : p = (1 - q⁻¹)⁻¹ := by
  simp_rw [← inv_eq_iff_eq_inv]
  exact (ENNReal.cancel_of_ne hpq.right_inv_ne_top).eq_tsub_of_add_eq hpq.inv_add_inv_conj

lemma right_eq (hpq : p.IsConjExponent q) : q = (1 - p⁻¹)⁻¹ := hpq.symm.left_eq

lemma inj_right (hpq : p.IsConjExponent q) (hpq' : p.IsConjExponent q') : q = q' := by
  rw [hpq.right_eq, hpq'.right_eq]

lemma inj_left (hpq : p.IsConjExponent q) (hpq' : p'.IsConjExponent q) : p = p' :=
  hpq.symm.inj_right hpq'.symm

lemma left_eq_left_iff_right_eq_right (hpq : p.IsConjExponent q) (hpq' : p'.IsConjExponent q') :
    p = p' ↔ q = q' := by
  constructor <;> rintro rfl <;> [apply inj_right; apply inj_left] <;> assumption

lemma one_top : (1 : ℝ≥0∞).IsConjExponent ∞ := ⟨by simp⟩

lemma top_one : (∞ : ℝ≥0∞).IsConjExponent 1 := ⟨by simp⟩

lemma left_eq_one_iff (hpq : p.IsConjExponent q) : p = 1 ↔ q = ∞ :=
  hpq.left_eq_left_iff_right_eq_right .one_top

lemma left_eq_top_iff (hpq : p.IsConjExponent q) : p = ∞ ↔ q = 1 :=
  (left_eq_one_iff hpq.symm).symm

lemma one_lt_left_iff (hpq : p.IsConjExponent q) : 1 < p ↔ q ≠ ∞ := by
  rw [← not_iff_not, not_lt, ne_eq, not_not, hpq.one_le_left.le_iff_eq, hpq.left_eq_one_iff]

lemma left_ne_top_iff (hpq : p.IsConjExponent q) : p ≠ ∞ ↔ 1 < q :=
  (one_lt_left_iff hpq.symm).symm

lemma _root_.NNReal.IsConjExponent.coe_ennreal {p q : ℝ≥0} (hpq : p.IsConjExponent q) :
    (p : ℝ≥0∞).IsConjExponent q where
  inv_add_inv_conj := by
    have := hpq.symm.ne_zero
    have := hpq.ne_zero
    rw_mod_cast [hpq.inv_add_inv_conj]

lemma toNNReal {p q : ℝ≥0∞} (hp : p ≠ ∞) (hq : q ≠ ∞) (hpq : p.IsConjExponent q) :
    p.toNNReal.IsConjExponent q.toNNReal where
  one_lt := by
    rwa [← coe_lt_coe, coe_toNNReal hp, coe_one, hpq.one_lt_left_iff]
  inv_add_inv_conj := by
    rw [← coe_inj, coe_add, coe_inv, coe_inv, coe_one, coe_toNNReal hp, coe_toNNReal hq,
      hpq.inv_add_inv_conj]
    · exact (toNNReal_ne_zero).mpr ⟨hpq.right_ne_zero, hq⟩
    · exact (toNNReal_ne_zero).mpr ⟨hpq.left_ne_zero, hp⟩

lemma mul_eq_add (hpq : p.IsConjExponent q) : p * q = p + q := by
  induction p using recTopCoe
  . simp [hpq.right_ne_zero]
  induction q using recTopCoe
  . simp [hpq.left_ne_zero]
  norm_cast
  exact hpq.toNNReal coe_ne_top coe_ne_top |>.mul_eq_add

lemma induction
    (P : (p q : ℝ≥0∞) → (p.IsConjExponent q) → Prop)
    (nnreal : ∀ ⦃p q : ℝ≥0⦄, (h : p.IsConjExponent q) → P p q h.coe_ennreal)
    (one : P 1 ∞ one_top) (infty : P ∞ 1 top_one) {p q : ℝ≥0∞} (h : p.IsConjExponent q) :
    P p q h := by
  induction p using recTopCoe
  . simp_rw [h.left_eq_top_iff.mp rfl, infty]
  induction q using recTopCoe
  . simp_rw [h.left_eq_one_iff.mpr rfl, one]
  exact nnreal <| h.toNNReal coe_ne_top coe_ne_top

lemma induction_symm
    (P : (p q : ℝ≥0∞) → (p.IsConjExponent q) → Prop)
    (nnreal : ∀ ⦃p q : ℝ≥0⦄, (h : p.IsConjExponent q) → p ≤ q → P p q h.coe_ennreal)
    (one : P 1 ∞ one_top)
    (symm : ∀ ⦃p q : ℝ≥0∞⦄, (h : p.IsConjExponent q) → P p q h → P q p h.symm)
    {p q : ℝ≥0∞} (h : p.IsConjExponent q) : P p q h := by
  induction h using IsConjExponent.induction
  case nnreal p q h =>
    rcases le_total p q with hpq|hqp
    · exact nnreal h hpq
    · exact symm h.coe_ennreal.symm (nnreal h.symm hqp)
  case one => exact one
  case infty => exact symm .one_top one

/- Versions of Hölder's inequality.
Note that the hard case already exists as `ENNReal.lintegral_mul_le_Lp_mul_Lq`. -/

lemma _root_.ContinuousLinearMap.le_opNNNorm₂ (L : E₁ →L[𝕜] E₂ →L[𝕜] E₃) (x : E₁) (y : E₂) :
    ‖L x y‖₊ ≤ ‖L‖₊ * ‖x‖₊ * ‖y‖₊ := L.le_opNorm₂ x y

lemma _root_.ENNReal.lintegral_mul_le_one_top (μ : Measure α) {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
  ∫⁻ (a : α), (f * g) a ∂μ ≤ (∫⁻ (a : α), f a ∂μ) * (essSup g μ) := by
    calc ∫⁻ (a : α), (f * g) a ∂μ = ∫⁻ (a : α), (f * g) a ∂μ := rfl
    _ ≤ ∫⁻ (a : α), f a * (essSup g μ) ∂μ := by
      apply MeasureTheory.lintegral_mono_ae
      rw [Filter.eventually_iff, ← Filter.exists_mem_subset_iff]
      use {a | g a ≤ essSup g μ}
      rw [← Filter.eventually_iff]
      exact ⟨ae_le_essSup _, by simp; intro _ ha; apply ENNReal.mul_left_mono ha⟩
    _ = (∫⁻ (a : α), f a ∂μ) * (essSup g μ) := by
      rw [lintegral_mul_const'' _ hf]

lemma _root_.ENNReal.lintegral_norm_mul_le_one_top (μ : Measure α) {f : α → E₁} {g : α → E₂}
    (hf : AEMeasurable f μ) : ∫⁻ a, ‖f a‖₊ * ‖g a‖₊ ∂μ ≤ snorm f 1 μ * snorm g ⊤ μ := by
      simp [snorm, snorm', snormEssSup]
      apply lintegral_mul_le_one_top _ hf.ennnorm

theorem lintegral_mul_le (hpq : p.IsConjExponent q) (μ : Measure α) {f : α → E₁} {g : α → E₂}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, ‖L (f a) (g a)‖₊ ∂μ ≤ ‖L‖₊ * snorm f p μ * snorm g q μ := by
  calc ∫⁻ a, ‖L (f a) (g a)‖₊ ∂μ ≤ ∫⁻ a, ‖L‖₊ * (‖f a‖₊ * ‖g a‖₊) ∂μ := by
        simp_rw [← mul_assoc]; exact lintegral_mono_nnreal fun a ↦ L.le_opNNNorm₂ (f a) (g a)
    _ = ‖L‖₊ * ∫⁻ a, ‖f a‖₊ * ‖g a‖₊ ∂μ := lintegral_const_mul' _ _ coe_ne_top
    _ ≤ ‖L‖₊ * (snorm f p μ * snorm g q μ) := ?_
    _ = ‖L‖₊ * snorm f p μ * snorm g q μ := by rw [mul_assoc]
  gcongr
  induction hpq using IsConjExponent.induction
  case nnreal p q hpq =>
    calc
      ∫⁻ a, ‖f a‖₊ * ‖g a‖₊ ∂μ = ∫⁻ a, ((‖f ·‖₊) * (‖g ·‖₊)) a ∂μ := by
        apply lintegral_congr
        simp only [Pi.mul_apply, coe_mul, implies_true]
      _ ≤ snorm f p μ * snorm g q μ := by
        simp only [coe_mul, snorm, coe_eq_zero, coe_ne_top, ↓reduceIte, coe_toReal, mul_ite, mul_zero, ite_mul, zero_mul, hpq.ne_zero, hpq.symm.ne_zero, snorm']
        apply ENNReal.lintegral_mul_le_Lp_mul_Lq _ (NNReal.isConjExponent_coe.mpr hpq)
        . apply hf.ennnorm
        . apply hg.ennnorm
  case one => exact lintegral_norm_mul_le_one_top _ hf
  case infty =>
    calc
      ∫⁻ a, ‖f a‖₊ * ‖g a‖₊ ∂μ = ∫⁻ a, ‖g a‖₊ * ‖f a‖₊ ∂μ := by simp_rw [mul_comm]
    _ ≤ snorm f ⊤ μ * snorm g 1 μ := by rw [mul_comm]; exact lintegral_norm_mul_le_one_top _ hg

theorem integrable_bilin (hpq : p.IsConjExponent q) (μ : Measure α) {f : α → E₁} {g : α → E₂}
    (hf : Memℒp f p μ) (hg : Memℒp g q μ) :
    Integrable (fun a ↦ L (f a) (g a)) μ := by
  use L.aestronglyMeasurable_comp₂ hf.aestronglyMeasurable hg.aestronglyMeasurable
  apply lintegral_mul_le L hpq μ hf.aestronglyMeasurable.aemeasurable
    hg.aestronglyMeasurable.aemeasurable |>.trans_lt
  exact ENNReal.mul_lt_top (ENNReal.mul_ne_top coe_ne_top hf.snorm_ne_top) hg.snorm_ne_top

end IsConjExponent
end ENNReal

end

section
namespace MeasureTheory
namespace Lp

variable {α E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {p q : ℝ≥0∞}
  {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ  E₃] [FiniteDimensional ℝ  E₃]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E₁] [BorelSpace E₁]
  [MeasurableSpace E₂] [BorelSpace E₂]
  [MeasurableSpace E₃] [BorelSpace E₃]
  (L : E₁ →L[ℝ] E₂ →L[ℝ] E₃)

variable
  [hpq : Fact (p.IsConjExponent q)] [h'p : Fact (p < ∞)]
  [hp : Fact (1 ≤ p)] [hq : Fact (1 ≤ q)] -- note: these are superfluous, but it's tricky to make them instances.

lemma hp₀ : p ≠ 0 := by have := by calc 0 < 1 := by norm_num
                                        _ ≤ p := hp.out
                        apply ne_zero_of_lt this
lemma hpᵢ : p ≠ ∞ := by apply lt_top_iff_ne_top.mp h'p.out
lemma hq₀ : q ≠ 0 := by have := by calc 0 < 1 := by norm_num
                                        _ ≤ q := hq.out
                        apply ne_zero_of_lt this
lemma hq₀' : ¬ q = 0 := hq₀

lemma is_conj_exponent : p + q = p*q := hpq.out.mul_eq_add.symm

lemma is_conj_exponent' (hqᵢ : q ≠ ∞) : p.toReal + q.toReal = p.toReal*q.toReal := by
  rw[←toReal_add hpᵢ hqᵢ]
  rw[←toReal_mul]
  congr
  exact is_conj_exponent

open ENNReal.IsConjExponent
open ContinuousLinearMap
open Memℒp

section BasicFunctions

def step' : ℝ → ℝ := Set.piecewise {x | x ≤ 0} 0 1

@[fun_prop]
theorem measurable_step' : Measurable step' := by
  apply Measurable.piecewise
  . apply measurableSet_le
    . apply measurable_id
    . apply measurable_const
  . apply measurable_const
  . apply measurable_const

lemma sign_eq_step : Real.sign = fun x => step' x - step' (-x) := by
  ext x
  simp only [Real.sign, step']
  by_cases h₁ : x < 0
  . have h₂ : x ≤ 0 := by linarith
    have h₃ : ¬ 0 ≤ x := by linarith
    simp [h₁, h₂, h₃]
  . by_cases h₂ : 0 < x
    . have h₃ : 0 ≤ x := by linarith
      have h₄ : ¬ x ≤ 0 := by linarith
      simp[h₁, h₂, h₃, h₄]
    . have h₃ : x = 0 := by linarith
      simp[h₁, h₂, h₃]

theorem measurable_sign : Measurable (Real.sign : ℝ → ℝ) := by
  rw[sign_eq_step]
  fun_prop

@[simp]
theorem abs_of_sign (x) : |Real.sign x| = if x = 0 then 0 else 1 := by
  dsimp[_root_.abs, Real.sign]
  by_cases h₁ : x < 0
  . have h₂ : x ≠ 0 := by linarith
    simp[h₁, h₂]
  . by_cases h₂ : x = 0
    . simp[h₁, h₂]
    . have h₃ : 0 < x := by apply lt_of_le_of_ne; simp at h₁; exact h₁; symm; exact h₂
      simp[h₁, h₂, h₃]
@[simp]
theorem nnnorm_of_sign (x) : ‖Real.sign x‖₊ = if x = 0 then 0 else 1 := by
  ext
  rw [coe_nnnorm, norm_eq_abs, abs_of_sign, apply_ite toReal]
  rfl

def rpow' (y : ℝ) (x : ℝ≥0) : ℝ≥0 := NNReal.rpow x y

theorem rpow'_eq_rpow (x : ℝ≥0) (y : ℝ) : rpow' y x = x^y := rfl

theorem measurable_rpow'_const (c : ℝ) : Measurable (rpow' c) := by
  apply Measurable.pow (f := fun x => x) (g := fun _ => c)
  . apply measurable_id
  . apply measurable_const

@[simp]
theorem rpow_eq_one_iff (x : ℝ≥0∞) (y : ℝ) (hy : y > 0) : x^y = (1 : ℝ≥0∞) ↔ x = 1 := by
  constructor; swap; intro h; rw[h]; apply ENNReal.one_rpow
  intro h
  rw[←ENNReal.one_rpow y] at h
  apply le_antisymm <;> {apply (ENNReal.rpow_le_rpow_iff hy).mp; rw[h]}

@[simp]
theorem rpow_div_eq_one_iff (x : ℝ≥0∞) (y : ℝ) (hy : y > 0) : x^(1/y) = (1 : ℝ≥0∞) ↔ x = 1 := by
  have : 1/y > 0 := by simp[hy]
  rw[rpow_eq_one_iff x (1/y) this]

lemma toNNReal_of_norm_eq_nnnorm (x : ℝ) : ‖x‖.toNNReal = ‖x‖₊ := by
  calc _ = ‖‖x‖‖₊ := by apply toNNReal_eq_nnnorm_of_nonneg; apply norm_nonneg
       _ = _ := by simp

end BasicFunctions


theorem integral_mul_le (hpq : p.IsConjExponent q) (μ : Measure α) {f : Lp E₁ p μ} {g : Lp E₂ q μ}
    : ∫ a, ‖L (f a) (g a)‖ ∂μ ≤ ‖L‖ * ‖f‖ * ‖g‖ := by

    have : AEStronglyMeasurable (fun x => L (f x) (g x)) μ :=
                          by apply L.aestronglyMeasurable_comp₂
                             apply (Lp.memℒp f).aestronglyMeasurable
                             apply (Lp.memℒp g).aestronglyMeasurable
    rw[integral_norm_eq_lintegral_nnnorm this]

    have : (‖L‖₊ * (snorm f p μ) * (snorm g q μ)).toReal = ‖L‖ * ‖f‖ * ‖g‖ := by
              calc _ = ‖L‖₊.toReal * (snorm f p μ).toReal * (snorm g q μ).toReal := by simp
                   _ = ‖L‖ * ‖f‖ * ‖g‖                                           := by congr
    rw[←this]

    have : ∫⁻ (a : α), ↑‖(L (f a)) (g a)‖₊ ∂μ
              ≤ ↑‖L‖₊ * snorm (f) p μ * snorm (g) q μ := by apply lintegral_mul_le L hpq μ
                                                            . apply aestronglyMeasurable_iff_aemeasurable.mp
                                                              apply (Lp.memℒp f).aestronglyMeasurable
                                                            . apply aestronglyMeasurable_iff_aemeasurable.mp
                                                              apply (Lp.memℒp g).aestronglyMeasurable
    gcongr
    apply mul_ne_top; apply mul_ne_top
    . simp[this]
    . apply snorm_ne_top f
    . apply snorm_ne_top g

variable (μ) in
theorem snorm_eq_sup_abs'' (hμ : SigmaFinite μ) (g : Lp ℝ ∞ μ) :
              ‖g‖ = sSup ((fun f => ‖∫ x, (f x) * (g x) ∂μ‖) '' {(f : Lp ℝ 1 μ) | ‖f‖ ≤ 1}) := by
  -- we need μ to be σ-finite
  sorry

def to_conjᵢ (g : Lp ℝ q μ) : α → ℝ :=
    fun x => Real.sign (g x) * (rpow' (q.toReal-1) ‖g x‖₊) * ‖g‖₊^(1- q.toReal)

theorem conjᵢ_aestrongly_measurable (g : Lp ℝ q μ) : AEStronglyMeasurable (to_conjᵢ g) μ := by
  apply (aestronglyMeasurable_iff_aemeasurable (μ := μ)).mpr
  unfold to_conjᵢ
  apply AEMeasurable.mul
  . apply AEMeasurable.mul
    . apply Measurable.comp_aemeasurable'
      . apply measurable_sign
      . exact (Lp.memℒp g).aestronglyMeasurable.aemeasurable
    . apply Measurable.comp_aemeasurable'
      . apply measurable_coe_nnreal_real
      . apply Measurable.comp_aemeasurable'
        . apply measurable_rpow'_const
        . apply Measurable.comp_aemeasurable'
          . apply measurable_nnnorm
          . exact (Lp.memℒp g).aestronglyMeasurable.aemeasurable
  . apply aemeasurable_const

-- theorem abs_conjᵢ (g : Lp ℝ q μ) (hq₁ : q ≠ 1) (x) : |to_conjᵢ g x| = |g x|^(q.toReal-1) * ‖g‖^(1- q.toReal) := by
--   dsimp [to_conjᵢ, rpow']
--   rw[abs_mul, abs_mul]

--   have : |‖g‖^(1 - q.toReal)| = ‖g‖^(1 - q.toReal) := by apply abs_eq_self.mpr
--                                                          apply rpow_nonneg
--                                                          apply norm_nonneg
--   rw[this]
--   congr
--   have : |(|g x|^((q.toReal - 1)))| = |g x|^((q.toReal - 1)) := by simp
--                                                                    apply rpow_nonneg
--                                                                    apply abs_nonneg
--   rw[this]

--   by_cases h : g x = 0
--   . simp[h]; symm
--     apply (rpow_eq_zero_iff_of_nonneg ?_).mpr; swap; trivial
--     constructor; trivial
--     apply sub_ne_zero_of_ne
--     contrapose! hq₁
--     apply (toReal_eq_one_iff q).mp hq₁

--   . conv_rhs => rw[←one_mul (|g x|^((q.toReal - 1)))]
--     congr
--     rw[abs_of_sign]
--     simp[h]

theorem nnnorm_conjᵢ (g : Lp ℝ q μ) (hq₁ : q ≠ 1) (x)
    : ‖to_conjᵢ g x‖₊ = ‖g x‖₊^(q.toReal-1) * ‖g‖₊^(1- q.toReal) := by
  sorry

theorem nnnorm_conjᵢ' (g : Lp ℝ q μ) (hq₁ : q ≠ 1) (x)
    : ofNNReal ‖to_conjᵢ g x‖₊ = ofNNReal (‖g x‖₊^(q.toReal-1) * ‖g‖₊^(1- q.toReal)) := by
  congr
  exact nnnorm_conjᵢ g hq₁ x

-- theorem pow_abs_conjᵢ (g : Lp ℝ q μ) (hq₁ : q ≠ 1) (hqᵢ : q ≠ ∞) (x) : |to_conjᵢ g x|^p.toReal = |g x|^q.toReal * ‖g‖^(-q.toReal) := by

--   rw[abs_conjᵢ g hq₁ x, Real.mul_rpow,
--      ←(Real.rpow_mul ?_ _ _), _root_.sub_mul, one_mul,
--      ←(Real.rpow_mul ?_ _ _), _root_.sub_mul, one_mul]

--   have : q.toReal*p.toReal - p.toReal = q.toReal := by
--     calc _ = q.toReal*p.toReal - p.toReal - q.toReal + q.toReal       := by simp
--          _ = q.toReal*p.toReal - (p.toReal + q.toReal) + q.toReal     := by rw[←sub_add_eq_sub_sub]
--          _ = p.toReal*q.toReal - (p.toReal + q.toReal) + q.toReal     := by rw[mul_comm]
--          _ = (p.toReal + q.toReal) - (p.toReal + q.toReal) + q.toReal := by rw[is_conj_exponent' hqᵢ]
--          _ = 0 + q.toReal                                             := by simp
--          _ = _                                                        := by simp
--   rw[this]
--   have : p.toReal - q.toReal*p.toReal = -q.toReal := by
--     calc _ = -(q.toReal*p.toReal - p.toReal) := by rw[neg_sub]
--          _ = _  := by rw[this]
--   rw[this]

--   apply norm_nonneg
--   apply abs_nonneg
--   apply rpow_nonneg
--   apply abs_nonneg
--   apply rpow_nonneg
--   apply norm_nonneg

theorem pow_nnnorm_conjᵢ (g : Lp ℝ q μ) (hq₁ : q ≠ 1) (hqᵢ : q ≠ ∞) (x)
    : (‖to_conjᵢ g x‖₊ : ℝ≥0∞) ^ p.toReal = (‖g x‖₊ : ℝ≥0∞) ^ q.toReal * ‖g‖₊ ^ (-q.toReal) := by
  sorry

def to_conj₁ (g : Lp ℝ 1 μ) : α → ℝ := fun x => Real.sign (g x)

theorem conj₁_aestrongly_measurable (g : Lp ℝ 1 μ) : AEStronglyMeasurable (to_conj₁ g) μ := by
  apply (aestronglyMeasurable_iff_aemeasurable (μ := μ)).mpr
  apply Measurable.comp_aemeasurable' (f := g)
  . apply measurable_sign
  . apply aestronglyMeasurable_iff_aemeasurable.mp
    exact (Lp.memℒp g).aestronglyMeasurable

-- def to_conj (g : Lp ℝ q μ) : α → ℝ := if q = 1 then to_conj₁ g else to_conjᵢ g

theorem abs_conj₁ (g : Lp ℝ 1 μ) (x) : |to_conj₁ g x| = if g x = 0 then 0 else 1 := by
  apply abs_of_sign

variable (p) in
theorem conjᵢ_snorm' (g : Lp ℝ q μ) (hq₁ : q ≠ 1) (hqᵢ : q ≠ ∞) :
  (snorm' (to_conjᵢ g) p.toReal μ).toReal = ‖g‖^(q.toReal/p.toReal) := by

  dsimp only [snorm']
  #check pow_nnnorm_conjᵢ (p := p) g hq₁ hqᵢ

  conv =>
    lhs
    pattern ↑‖to_conjᵢ g a‖₊ ^ p.toReal
    rw[pow_nnnorm_conjᵢ (p := p) g hq₁ hqᵢ a]

  sorry

variable (p q μ) in
theorem snorm_eq_sup_abs' (g : Lp ℝ q μ) (hqᵢ : q ≠ ∞) :
              ‖g‖ = sSup ((fun f => ‖∫ x, (f x) * (g x) ∂μ‖) '' {(f : Lp ℝ p μ) | ‖f‖ ≤ 1}) := by
  -- basic facts about p and q
  have hpq := hpq.out

  have hp := hp.out
  have h'p := h'p.out
  have hpᵢ : p ≠ ∞ := by apply lt_top_iff_ne_top.mp h'p
  have hp₀ : p ≠ 0 := by have := by calc 0 < 1   := by norm_num
                                         _ ≤ p   := hp
                         apply ne_zero_of_lt this
  have hq := hq.out
  -- let h'q := h'q.out
  -- let hqᵢ : q ≠ ∞ := by apply lt_top_iff_ne_top.mp h'q
  have hq₀ : q ≠ 0 := by have := by calc 0 < 1   := by norm_num
                                         _ ≤ q   := hq
                         apply ne_zero_of_lt this

  -- construction of the function f₀'
  let F := (fun f : Lp ℝ p μ => ‖∫ x, (f x) * (g x) ∂μ‖)
  let S := {f : Lp ℝ p μ | ‖f‖ ≤ 1}

  #check integral_congr_ae

  apply le_antisymm; swap
  . apply Real.sSup_le; swap; apply norm_nonneg
    intro x hx
    rcases hx with ⟨f, hf, rfl⟩
    simp at hf; dsimp only

    calc _ ≤ ∫ x, ‖f x * g x‖ ∂μ             := by apply norm_integral_le_integral_norm
         _ = ∫ x, ‖(mul ℝ ℝ) (f x) (g x)‖ ∂μ := by simp
         _ ≤ ‖(mul ℝ ℝ)‖ * ‖f‖ * ‖g‖         := by apply integral_mul_le; exact hpq
         _ = ‖f‖ * ‖g‖                       := by simp
         _ ≤ 1 * ‖g‖                         := by gcongr
         _ = ‖g‖                             := by simp

  --
  . let h₁ := fun (y : ℝ) => y^(q.toReal-1)
    have h₁_cont : Continuous h₁ := by dsimp only [h₁]
                                       apply Continuous.rpow_const
                                       apply continuous_id
                                       intro _; right; simp;
                                       rw[←ENNReal.one_toReal]
                                       gcongr
                                       exact hqᵢ

    let h₂ := fun (y : ℝ) => h₁ (abs y)
    have h₂_cont : Continuous h₂ := by apply Continuous.comp';
                                       apply h₁_cont;
                                       apply Continuous.abs;
                                       apply continuous_id

    let h := fun (y : ℝ) => (Real.sign y) * (h₂ y) * ‖g‖^(q.toReal-1)
    let f₀ := fun (x : α) => h (g x)

    have h_meas : Measurable h := by apply Measurable.mul; swap
                                     . apply measurable_const
                                     . apply Measurable.mul
                                       . apply measurable_sign
                                       . apply Continuous.measurable; apply h₂_cont

    have hf₀_meas : AEStronglyMeasurable f₀ μ := by apply aestronglyMeasurable_iff_aemeasurable.mpr
                                                    dsimp[f₀]
                                                    apply Measurable.comp_aemeasurable' (f := g) (g := h)
                                                    . exact h_meas
                                                    . apply aestronglyMeasurable_iff_aemeasurable.mp
                                                      exact (Lp.memℒp g).aestronglyMeasurable

    #check integral_norm_eq_lintegral_nnnorm hf₀_meas
    #check (rpow_left_inj _ _ _).mp

    have hf_snorm : snorm f₀ p μ = 1 := by simp[snorm, hp₀, hpᵢ]
                                           dsimp only [snorm']
                                            -- should be easy
                                           sorry

    have hf_memℒp : Memℒp f₀ p μ := by constructor
                                       . exact hf₀_meas
                                       . simp[hf_snorm]

    let f₀' := by apply toLp f₀
                  . constructor
                    . exact hf₀_meas
                    . apply lt_of_le_of_lt
                      . show snorm f₀ p μ ≤ 1
                        simp only [hf_snorm, le_refl]
                      . simp only [one_lt_top]

    have hf₀'_norm : ‖f₀'‖ = 1 := by sorry
    have hf₀'_int : ∫ x, (f₀' x) * (g x) ∂μ = ‖g‖ := by sorry

    . apply le_csSup
      . use ‖g‖
        intro x hx
        rcases hx with ⟨f, hf, rfl⟩
        simp at hf

        calc _ ≤ ∫ x, ‖f x * g x‖ ∂μ             := by apply norm_integral_le_integral_norm
            _ = ∫ x, ‖(mul ℝ ℝ) (f x) (g x)‖ ∂μ := by simp
            _ ≤ ‖(mul ℝ ℝ)‖ * ‖f‖ * ‖g‖         := by apply integral_mul_le; exact hpq
            _ = ‖f‖ * ‖g‖                       := by simp
            _ ≤ 1 * ‖g‖                         := by gcongr
            _ = ‖g‖                             := by simp
        -- this is duplicate code

      . use f₀'
        constructor
        . simp only [Set.mem_setOf_eq]; rw[hf₀'_norm]
        . dsimp only; rw[hf₀'_int]; simp only [norm_norm]

variable (p q μ) in
theorem snorm_eq_sup_abs (hμ : SigmaFinite μ) (g : Lp ℝ q μ):
              ‖g‖ = sSup ((fun f => ‖∫ x, (f x) * (g x) ∂μ‖) '' {(f : Lp ℝ p μ) | ‖f‖ ≤ 1}) := by

  by_cases hqᵢ : q ≠ ⊤; swap
  . simp at hqᵢ
    have hp₁ : p = 1 := by {
      rw[left_eq_one_iff, ← hqᵢ]
      exact hpq.out
    }
    subst hqᵢ; subst hp₁

    apply snorm_eq_sup_abs'' μ hμ g

  . apply snorm_eq_sup_abs' p q μ g hqᵢ

/- The map sending `g` to `f ↦ ∫ x, L (g x) (f x) ∂μ` induces a map on `L^q` into
`Lp E₂ p μ →L[ℝ] E₃`. Generally we will take `E₃ = ℝ`. -/
variable (p μ) in
def toDual (g : Lp E₁ q μ) : Lp E₂ p μ →L[ℝ] E₃ := by{

  let F : Lp E₂ p μ → E₃ := fun f ↦ ∫ x, L (g x) (f x) ∂μ

  have : IsBoundedLinearMap ℝ F := by{
    exact {
      map_add := by{
        intro f₁ f₂
        simp[F]
        rw[← integral_add]
        · apply integral_congr_ae
          filter_upwards [coeFn_add f₁ f₂] with a ha
          norm_cast
          rw[ha]
          simp
        · exact ENNReal.IsConjExponent.integrable_bilin L hpq.out.symm μ (Lp.memℒp g) (Lp.memℒp f₁)
        · exact ENNReal.IsConjExponent.integrable_bilin L hpq.out.symm μ (Lp.memℒp g) (Lp.memℒp f₂)
        }

      map_smul := by{
        intro m f
        simp[F]
        rw[← integral_smul]
        apply integral_congr_ae
        filter_upwards [coeFn_smul m f] with a ha
        rw[ha]
        simp
        }

      bound := by{
        suffices henough : ∃ M, ∀ (x : ↥(Lp E₂ p μ)), ‖F x‖ ≤ M * ‖x‖ from ?_
        . let ⟨M, hM⟩ := henough; clear henough

          by_cases hM_le_zero : M ≤ 0
          . use 1; constructor; linarith; intro f
            calc ‖F f‖ ≤ M * ‖f‖ := hM f
                 _     ≤ 1 * ‖f‖ := by apply mul_le_mul_of_nonneg_right; linarith
                                       apply norm_nonneg
          . simp at hM_le_zero; use M

        simp only [F]
        use ‖L‖ * ‖g‖
        intro f
        calc ‖∫ (x : α), (L (g x)) (f x) ∂μ‖ ≤ ∫ (x : α), ‖L (g x) (f x)‖ ∂μ := by apply norm_integral_le_integral_norm
             _ ≤ ‖L‖ * ‖g‖ * ‖f‖ := ?_

        apply integral_mul_le L hpq.out.symm
      }
    }
  }

  apply IsBoundedLinearMap.toContinuousLinearMap this
}

/- The map sending `g` to `f ↦ ∫ x, (f x) * (g x) ∂μ` is a linear isometry. -/
variable (L' : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) (L'mul : ∀ x y, L' x y = x * y) (L'norm_one : ‖L'‖ = 1) in
def toDualₗᵢ' : Lp ℝ q μ →ₗᵢ[ℝ] Lp ℝ p μ →L[ℝ] ℝ where
  toFun := toDual _ _ L'
  map_add':= by{
    intro g₁ g₂
    simp[toDual, IsBoundedLinearMap.toContinuousLinearMap, IsBoundedLinearMap.toLinearMap]
    ext f
    simp
    rw[← integral_add]
    · apply integral_congr_ae
      filter_upwards [coeFn_add g₁ g₂] with a ha
      norm_cast
      rw[ha]
      simp
    · exact ENNReal.IsConjExponent.integrable_bilin L' hpq.out.symm μ (Lp.memℒp g₁) (Lp.memℒp f)
    · exact ENNReal.IsConjExponent.integrable_bilin L' hpq.out.symm μ (Lp.memℒp g₂) (Lp.memℒp f)
  }
  map_smul':= by{
    intro m g
    simp[toDual, IsBoundedLinearMap.toContinuousLinearMap, IsBoundedLinearMap.toLinearMap]
    ext f
    simp
    rw[← integral_mul_left] -- mul vs smul
    apply integral_congr_ae
    filter_upwards [coeFn_smul m g] with a ha
    rw[ha]
    simp[L'mul]; ring
  }
  norm_map' := by {
    intro g
    conv_lhs => simp[Norm.norm]
    apply ContinuousLinearMap.opNorm_eq_of_bounds
    . simp
    . intro f
      calc ‖(toDual p μ L' g) f‖ ≤ ∫ x, ‖L' (g x) (f x)‖ ∂μ := by apply norm_integral_le_integral_norm
           _ ≤ ‖L'‖ * ‖g‖ * ‖f‖ := by apply integral_mul_le L' hpq.out.symm
           _ = ‖g‖ * ‖f‖ := by simp[L'norm_one]
           _ = _ := by aesop
    . intro N Nnneg
      intro hbound


      let f := fun (x : α) => (Real.sign (g x))

      #check snorm'_lim_eq_lintegral_liminf
      sorry
      -- f = g ^ q-1 have := hbound

    -- apply le_antisymm
    -- . apply ContinuousLinearMap.opNorm_le_bound; apply norm_nonneg
    --   intro f
    --   simp
    --   calc ‖(toDual p μ L' g) f‖ = ‖∫ x, L' (g x) (f x) ∂μ‖ := by congr
    --        _ ≤ ∫ x, ‖L' (g x) (f x)‖ ∂μ := by apply norm_integral_le_integral_norm
    --        _ ≤ ‖L'‖ * ‖g‖ * ‖f‖ := by apply integral_mul_le; exact hpq.out.symm
    --        _ = ‖g‖ * ‖f‖ := by simp[L'norm_one]

    -- . simp[Norm.norm, ContinuousLinearMap.opNorm]
    --   -- apply UniformSpace.le_sInf (α := ℝ)
    --   -- #check (@sInf ℝ).le
    --   sorry
  }

/- The map sending `g` to `f ↦ ∫ x, L (f x) (g x) ∂μ` is a linear isometry. -/
variable (p q μ) in
def toDualₗᵢ : Lp E₁ q μ →ₗᵢ[ℝ] Lp E₂ p μ →L[ℝ] E₃ where

  toFun := toDual _ _ L
  map_add':= by{
    intro g₁ g₂
    simp[toDual, IsBoundedLinearMap.toContinuousLinearMap, IsBoundedLinearMap.toLinearMap]
    ext f
    simp
    rw[← integral_add]
    · apply integral_congr_ae
      filter_upwards [coeFn_add g₁ g₂] with a ha
      norm_cast
      rw[ha]
      simp
    · exact ENNReal.IsConjExponent.integrable_bilin L hpq.out.symm μ (Lp.memℒp g₁) (Lp.memℒp f)
    · exact ENNReal.IsConjExponent.integrable_bilin L hpq.out.symm μ (Lp.memℒp g₂) (Lp.memℒp f)
  }
  map_smul':= by{
    intro m g
    simp[toDual, IsBoundedLinearMap.toContinuousLinearMap, IsBoundedLinearMap.toLinearMap]
    ext f
    simp
    rw[← integral_smul]
    apply integral_congr_ae
    filter_upwards [coeFn_smul m g] with a ha
    rw[ha]
    simp
  }
  norm_map' := by {
    sorry
  }

/- The map sending `g` to `f ↦ ∫ x, L (f x) (g x) ∂μ` is a linear isometric equivalence.  -/
variable (p q μ) in
def dualIsometry (L : E₁ →L[ℝ] Dual ℝ E₂) :
    Dual ℝ (Lp E₂ p μ) ≃ₗᵢ[ℝ] Lp E q μ :=
  sorry

end Lp
end MeasureTheory

end
