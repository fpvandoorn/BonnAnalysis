import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Analysis.NormedSpace.LinearIsometry
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Data.Real.Sign

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

lemma left_ne_zero (hpq : p.IsConjExponent q) : p ≠ 0 := zero_lt_one.trans_le hpq.one_le_left |>.ne'

lemma right_ne_zero (hpq : p.IsConjExponent q) : q ≠ 0 := hpq.symm.left_ne_zero

lemma left_inv_ne_top (hpq : p.IsConjExponent q) : p⁻¹ ≠ ∞ := by
  rw [inv_ne_top]
  exact hpq.left_ne_zero

lemma right_inv_ne_top (hpq : p.IsConjExponent q) : q⁻¹ ≠ ∞ := hpq.symm.left_inv_ne_top

lemma left_eq (hpq : p.IsConjExponent q) : p = (1 - q⁻¹)⁻¹ := by
  rw [← inv_eq_iff_eq_inv]
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
  induction p
  . simp [hpq.right_ne_zero]
  induction q
  . simp [hpq.left_ne_zero]
  exact_mod_cast hpq.toNNReal coe_ne_top coe_ne_top |>.mul_eq_add

lemma induction
    (P : (p q : ℝ≥0∞) → (p.IsConjExponent q) → Prop)
    (nnreal : ∀ ⦃p q : ℝ≥0⦄, (h : p.IsConjExponent q) → P p q h.coe_ennreal)
    (one : P 1 ∞ one_top) (infty : P ∞ 1 top_one) {p q : ℝ≥0∞} (h : p.IsConjExponent q) :
    P p q h := by
  induction p
  . simp_rw [h.left_eq_top_iff.mp rfl, infty]
  induction q
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

lemma _root_.ENNReal.lintegral_mul_le_one_top (μ : Measure α) {f g : α → ℝ≥0∞}
  (hf : AEMeasurable f μ) : ∫⁻ (a : α), (f * g) a ∂μ ≤ (∫⁻ (a : α), f a ∂μ) * (essSup g μ) := by
  calc ∫⁻ (a : α), (f * g) a ∂μ = ∫⁻ (a : α), (f * g) a ∂μ := rfl
  _ ≤ ∫⁻ (a : α), f a * (essSup g μ) ∂μ := by
    apply MeasureTheory.lintegral_mono_ae
    rw [Filter.eventually_iff, ← Filter.exists_mem_subset_iff]
    use {a | g a ≤ essSup g μ}
    rw [← Filter.eventually_iff]
    exact ⟨ae_le_essSup _, fun _ ha ↦ ENNReal.mul_left_mono ha⟩
  _ = (∫⁻ (a : α), f a ∂μ) * (essSup g μ) := by
    rw [lintegral_mul_const'' _ hf]

lemma _root_.ENNReal.lintegral_norm_mul_le_one_top (μ : Measure α) {f : α → E₁} {g : α → E₂}
    (hf : AEMeasurable f μ) : ∫⁻ a, ‖f a‖₊ * ‖g a‖₊ ∂μ ≤ snorm f 1 μ * snorm g ⊤ μ := by
      simp only [snorm, one_ne_zero, ↓reduceIte, one_ne_top, snorm', one_toReal, rpow_one, ne_eq,
        not_false_eq_true, div_self, top_ne_zero, snormEssSup]
      exact lintegral_mul_le_one_top _ hf.ennnorm

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
        exact ENNReal.lintegral_mul_le_Lp_mul_Lq _ (NNReal.isConjExponent_coe.mpr hpq) hf.ennnorm hg.ennnorm
  case one => exact lintegral_norm_mul_le_one_top _ hf
  case infty =>
    calc
      ∫⁻ a, ‖f a‖₊ * ‖g a‖₊ ∂μ = ∫⁻ a, ‖g a‖₊ * ‖f a‖₊ ∂μ := by simp_rw [mul_comm]
    _ ≤ snorm f ⊤ μ * snorm g 1 μ := by rw [mul_comm]; exact lintegral_norm_mul_le_one_top _ hg

theorem integrable_bilin (hpq : p.IsConjExponent q) (μ : Measure α) {f : α → E₁} {g : α → E₂}
    (hf : Memℒp f p μ) (hg : Memℒp g q μ) :
    Integrable (fun a ↦ L (f a) (g a)) μ := by
  use L.aestronglyMeasurable_comp₂ hf.aestronglyMeasurable hg.aestronglyMeasurable
  exact lintegral_mul_le L hpq μ hf.aestronglyMeasurable.aemeasurable
    hg.aestronglyMeasurable.aemeasurable |>.trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_ne_top coe_ne_top hf.snorm_ne_top) hg.snorm_ne_top)

end IsConjExponent

lemma toNNReal_eq_toNNreal_of_toReal (x : ℝ≥0∞) :
    x.toReal.toNNReal = x.toNNReal := by aesop

lemma rpow_of_to_ENNReal_of_NNReal_ne_top (x : ℝ≥0) (y : ℝ) (hynneg : y ≥ 0)
    : (x : ℝ≥0∞) ^ y ≠ ∞ := by aesop

lemma nnnorm_of_toReal_eq_toNNReal (x : ℝ≥0∞) : ‖x.toReal‖₊ = x.toNNReal := by
  ext1
  simp only [coe_nnnorm, norm_eq_abs, abs_toReal]
  rfl

def rpow' (y : ℝ) (x : ℝ≥0∞) : ℝ≥0∞ := ENNReal.rpow x y

theorem rpow'_eq_rpow (x : ℝ≥0∞) (y : ℝ) : rpow' y x = x^y := rfl

theorem measurable_rpow'_const (c : ℝ) : Measurable (rpow' c) := by
  apply Measurable.pow (f := fun x => x) (g := fun _ => c) <;> fun_prop

end ENNReal

end

section
namespace MeasureTheory
namespace Lp
open ENNReal.IsConjExponent

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

section  BasicFactsConjugateExponents

lemma p_ne_zero : p ≠ 0 := left_ne_zero hpq.out

lemma p_ne_top : p ≠ ∞ := lt_top_iff_ne_top.mp h'p.out

lemma p_ne_zero' : p.toReal ≠ 0 := toReal_ne_zero.mpr ⟨p_ne_zero (q := q), p_ne_top⟩

lemma p_gt_zero : p > 0 := by
  calc p ≥ 1 := hp.out
       _ > 0 := zero_lt_one' ℝ≥0∞

lemma p_gt_zero' : p.toReal > 0 := (toReal_pos_iff_ne_top p).mpr p_ne_top

lemma p_ge_zero : p ≥ 0 := zero_le p

lemma p_ge_zero' : p.toReal ≥ 0 := toReal_nonneg

lemma q_ne_zero : q ≠ 0 := right_ne_zero hpq.out

lemma q_ne_zero' (hqᵢ : q ≠ ∞) : q.toReal ≠ 0 := toReal_ne_zero.mpr ⟨q_ne_zero (p := p), hqᵢ⟩

lemma q_gt_zero : q > 0 := p_gt_zero

lemma q_gt_zero' (hqᵢ : q ≠ ∞) : q.toReal > 0 := (toReal_pos_iff_ne_top q).mpr hqᵢ

lemma q_ge_zero : q ≥ 0 := p_ge_zero

lemma q_ge_zero' : q.toReal ≥ 0 := p_ge_zero'

lemma q_gt_one : q > 1 := (left_ne_top_iff hpq.out).mp p_ne_top

lemma q_gt_one' (hqᵢ : q ≠ ∞) : q.toReal > 1 :=
  ENNReal.one_toReal ▸ (ENNReal.toReal_lt_toReal (Ne.symm top_ne_one) hqᵢ).mpr
    (q_gt_one (q := q) (p := p))

lemma q_ge_one : q ≥ 1 := by apply le_of_lt; exact q_gt_one (p := p)

lemma q_ge_one' (hqᵢ : q ≠ ∞) : q.toReal ≥ 1 :=
  ENNReal.one_toReal ▸ (ENNReal.toReal_le_toReal (Ne.symm top_ne_one) hqᵢ).mpr
    (q_ge_one (q := q) (p := p))

lemma q_sub_one_pos' (hqᵢ : q ≠ ∞) : q.toReal - 1 > 0 :=
  sub_pos.mpr (q_gt_one' (q := q) (p := p) hqᵢ)

lemma q_sub_one_nneg' (hqᵢ : q ≠ ∞) : q.toReal - 1 ≥ 0 := by
  linarith [q_sub_one_pos' (q := q) (p := p) hqᵢ]

lemma p_add_q : p + q = p * q := hpq.out.mul_eq_add.symm

lemma p_add_q' (hqᵢ : q ≠ ∞) : p.toReal + q.toReal = p.toReal*q.toReal := by
  rw [← toReal_add p_ne_top hqᵢ, ← toReal_mul]
  congr
  exact p_add_q

lemma q_div_p_ne_top (hqᵢ : q ≠ ∞) : q / p ≠ ∞ := by
  by_contra!
  have := (@ENNReal.div_eq_top q p).mp this
  contrapose! this
  exact ⟨fun _ ↦ p_ne_zero (q := q), fun _ ↦ by contradiction⟩

lemma q_div_p_add_one : q / p + 1 = q := by
  calc _ = q / p + p / p := by rw [ENNReal.div_self (p_ne_zero (q := q)) p_ne_top]
       _ = (q + p) / p := ENNReal.div_add_div_same
       _ = (p + q) / p := by rw [add_comm]
       _ = (p * q) / p := by rw [p_add_q]
       _ = (p * q) / (p * 1) := by rw [mul_one]
       _ = q / 1 := by rw [ENNReal.mul_div_mul_left _ _ (p_ne_zero (q := q)) p_ne_top]
       _ = q := div_one q

lemma q_div_p_add_one' (hqᵢ : q ≠ ∞) : q.toReal / p.toReal + 1 = q.toReal := by
  calc _ = (q / p).toReal + 1 := by rw [toReal_div]
       _ = (q / p + 1).toReal := by rw [toReal_add, one_toReal]; apply q_div_p_ne_top hqᵢ; simp
       _ = q.toReal := by rw [q_div_p_add_one]

lemma q_div_p_add_one'' (hqᵢ : q ≠ ∞) : q.toReal / p.toReal = q.toReal - 1 := by
  calc _ = q.toReal / p.toReal + 1 - 1 := Eq.symm (add_sub_cancel_right (q.toReal / p.toReal) 1)
       _ = q.toReal - 1 := by rw [q_div_p_add_one' hqᵢ]

end BasicFactsConjugateExponents

open ContinuousLinearMap
open Memℒp

section BasicFunctions

theorem snorm'_mul_const {p : ℝ} (hp : p > 0) (f : α → ℝ) (c : ℝ) :
    snorm' (fun x => f x * c) p μ = (snorm' f p μ) * ‖c‖₊ := by
  unfold snorm'; dsimp only; simp_all

  by_cases hc : c = 0
  . simp_all[hc, p_ne_zero']

  conv =>
    pattern (_ * _) ^ _
    rw [ENNReal.mul_rpow_of_ne_top]
    rfl
    · exact coe_ne_top
    · exact coe_ne_top

  rw [lintegral_mul_const']
  case neg.hr => simp_all

  by_cases hf : ∫⁻ (a : α), ↑‖f a‖₊ ^ p ∂μ = ∞
  . rw [hf]; simp_all

  rw [ENNReal.mul_rpow_of_ne_top hf]
  case neg.hy => simp_all;

  congr
  apply ENNReal.rpow_rpow_inv
  linarith

theorem nnnorm_toReal_eq_abs (x : ℝ) : ‖x‖₊.toReal = |x| := by rw [coe_nnnorm, norm_eq_abs]

def step' : ℝ → ℝ := Set.piecewise {x | x ≤ 0} 0 1

@[fun_prop]
theorem measurable_step' : Measurable step' :=
  Measurable.piecewise (measurableSet_le measurable_id measurable_const)
  (measurable_const) (measurable_const)

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
      simp [h₁, h₂, h₃, h₄]
    . have h₃ : x = 0 := by linarith
      simp [h₁, h₂, h₃]

theorem measurable_sign : Measurable (Real.sign : ℝ → ℝ) := by
  rw [sign_eq_step]
  fun_prop

@[simp]
theorem abs_of_sign (x) : |Real.sign x| = if x = 0 then 0 else 1 := by
  dsimp [_root_.abs, Real.sign]
  by_cases h₁ : x < 0
  . have h₂ : x ≠ 0 := by linarith
    simp [h₁, h₂]
  . by_cases h₂ : x = 0
    . simp [h₁, h₂]
    . have h₃ : 0 < x := by apply lt_of_le_of_ne; simp at h₁; exact h₁; symm; exact h₂
      simp [h₁, h₂, h₃]
@[simp]
theorem nnnorm_of_sign (x) : ‖Real.sign x‖₊ = if x = 0 then 0 else 1 := by
  ext
  rw [coe_nnnorm, norm_eq_abs, abs_of_sign, apply_ite toReal]
  rfl

theorem Real.self_mul_sign (x : ℝ) : x * x.sign = |x| := by
  by_cases hx₁ : x = 0
  . rw [hx₁, Real.sign_zero, mul_zero, abs_zero]
  . by_cases hx₂ : x > 0
    . rw [Real.sign_of_pos hx₂, mul_one, abs_of_pos hx₂]
    . have hx₃ : x < 0 := lt_of_le_of_ne (by linarith) hx₁
      rw [Real.sign_of_neg hx₃, mul_neg_one, abs_of_neg hx₃]

theorem rpow_of_nnnorm_of_sign (x y : ℝ) (hypos : y > 0)
    : (‖Real.sign x‖₊ : ℝ≥0∞) ^ y = if x = 0 then 0 else 1 := by aesop

def rpow' (y : ℝ) (x : ℝ≥0) : ℝ≥0 := NNReal.rpow x y

theorem rpow'_eq_rpow (x : ℝ≥0) (y : ℝ) : rpow' y x = x^y := rfl

theorem ennreal_rpow_of_nnreal (x : ℝ≥0) (y : ℝ)
    : (ENNReal.rpow x y).toNNReal = NNReal.rpow x y := by
  simp only [ENNReal.rpow_eq_pow, NNReal.rpow_eq_pow]
  rw [←ENNReal.toNNReal_rpow]
  simp only [ENNReal.toNNReal_coe]

theorem ennreal_rpow_of_nnreal' (x : ℝ≥0) (y : ℝ) (hynneg : y ≥ 0)
    : ENNReal.rpow x y = ofNNReal (NNReal.rpow x y) := by
  apply (ENNReal.toNNReal_eq_toNNReal_iff' _ _).mp <;> simp
  . rw [←ENNReal.toNNReal_rpow, ENNReal.toNNReal_coe]
  . exact fun _ ↦ hynneg

theorem measurable_rpow'_const (c : ℝ) : Measurable (rpow' c) :=
  Measurable.pow (f := fun x => x) (g := fun _ => c) measurable_id measurable_const

@[simp]
theorem rpow_eq_one_iff (x : ℝ≥0∞) (y : ℝ) (hy : y > 0) : x^y = (1 : ℝ≥0∞) ↔ x = 1 := by
  constructor; swap; intro h; rw [h]; apply ENNReal.one_rpow
  intro h
  rw [← ENNReal.one_rpow y] at h
  apply le_antisymm <;> {apply (ENNReal.rpow_le_rpow_iff hy).mp; rw [h]}

@[simp]
theorem rpow_div_eq_one_iff (x : ℝ≥0∞) (y : ℝ) (hy : y > 0) : x^(1/y) = (1 : ℝ≥0∞) ↔ x = 1 := by
  have : 1/y > 0 := by simp [hy]
  rw [rpow_eq_one_iff x (1/y) this]

lemma toNNReal_of_norm_eq_nnnorm (x : ℝ) : ‖x‖.toNNReal = ‖x‖₊ := by
  calc _ = ‖‖x‖‖₊ := toNNReal_eq_nnnorm_of_nonneg (norm_nonneg _)
       _ = _ := nnnorm_norm x

theorem mul_of_ae_eq {f f' g g' : α → ℝ≥0∞} (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g')
    : f * g =ᵐ[μ] f' * g' := by
  apply ae_iff.mpr
  apply measure_mono_null

  show {a | (f * g) a ≠ (f' * g') a} ⊆ {a | f a ≠ f' a} ∪ {a | g a ≠ g' a}

  . intro a ha
    by_contra!
    aesop
  . apply measure_union_null <;> assumption

theorem mul_of_ae_eq_one (f g: α → ℝ≥0∞) (hf : f =ᵐ[μ] 1) : f * g =ᵐ[μ] g := by
  conv =>
    rhs
    rw [←one_mul g]

  apply mul_of_ae_eq hf
  trivial

end BasicFunctions

-- Generalized version of Hölder's inequality.
theorem integral_mul_le (hpq : p.IsConjExponent q) (μ : Measure α) {f : Lp E₁ p μ} {g : Lp E₂ q μ}
    : ∫ a, ‖L (f a) (g a)‖ ∂μ ≤ ‖L‖ * ‖f‖ * ‖g‖ := by

  have : AEStronglyMeasurable (fun x => L (f x) (g x)) μ :=
    L.aestronglyMeasurable_comp₂ (Lp.memℒp f).aestronglyMeasurable (Lp.memℒp g).aestronglyMeasurable

  rw [integral_norm_eq_lintegral_nnnorm this]

  have : (‖L‖₊ * (snorm f p μ) * (snorm g q μ)).toReal = ‖L‖ * ‖f‖ * ‖g‖ := by
    calc _ = ‖L‖₊.toReal * (snorm f p μ).toReal * (snorm g q μ).toReal := by simp
         _ = ‖L‖ * ‖f‖ * ‖g‖                                           := by congr
  rw [←this]

  have : ∫⁻ (a : α), ↑‖(L (f a)) (g a)‖₊ ∂μ ≤ ↑‖L‖₊ * snorm (f) p μ * snorm (g) q μ := by
    apply lintegral_mul_le L hpq μ (aestronglyMeasurable_iff_aemeasurable.mp
      (Lp.memℒp f).aestronglyMeasurable) (aestronglyMeasurable_iff_aemeasurable.mp
        (Lp.memℒp g).aestronglyMeasurable)

  gcongr
  apply mul_ne_top; apply mul_ne_top
  . exact Ne.symm top_ne_coe
  . exact snorm_ne_top f
  . exact snorm_ne_top g

section conj_q_lt_top'

def conj_q_lt_top' {q : ℝ≥0∞} (g : Lp ℝ q μ) : α → ℝ :=
  fun x => Real.sign (g x) * (ENNReal.rpow' (q.toReal-1) ‖g x‖₊).toReal

theorem lint_conj_q_lt_top'_mul_self (hqᵢ : q ≠ ∞) {g : Lp ℝ q μ}
    : ∫⁻ (x : α), (conj_q_lt_top' g x).toNNReal * (g x).toNNReal ∂μ = ‖g‖₊ ^ q.toReal := by
  unfold conj_q_lt_top'
  unfold ENNReal.rpow'
  conv =>
    lhs
    congr
    . rfl
    . intro x
      simp
      congr
      . congr
        rw [mul_comm, Real.toNNReal_mul, ENNReal.toNNReal_eq_toNNreal_of_toReal]
        . rw [ENNReal.coe_rpow_of_nonneg]
          . rw [ENNReal.toNNReal_coe]
            rfl
          . apply q_sub_one_nneg' (p := p) hqᵢ
        . apply toReal_nonneg
      . rfl

  sorry

theorem int_conj_q_lt_top'_mul_self (hqᵢ : q ≠ ∞) {g : Lp ℝ q μ}
    : ‖∫ (x : α), (conj_q_lt_top' g) x * g x ∂μ‖ = ‖g‖ ^ q.toReal := by
  unfold conj_q_lt_top'
  unfold ENNReal.rpow'
  conv =>
    pattern _ * _
    rw [mul_assoc, mul_comm, mul_assoc]
    congr
    rfl
    rw [Real.self_mul_sign, ← nnnorm_toReal_eq_abs]
    rfl

  sorry

@[measurability]
theorem conj_q_lt_top'_aemeasurable (g : Lp ℝ q μ)
    : AEMeasurable (conj_q_lt_top' g) μ := by
  apply AEMeasurable.mul <;> apply Measurable.comp_aemeasurable'
  . exact measurable_sign
  . exact (Lp.memℒp g).aestronglyMeasurable.aemeasurable
  . exact ENNReal.measurable_toReal
  . exact Measurable.comp_aemeasurable' (ENNReal.measurable_rpow'_const _)
      (Measurable.comp_aemeasurable' (measurable_coe_nnreal_ennreal) (Measurable.comp_aemeasurable'
      (measurable_nnnorm) (Lp.memℒp g).aestronglyMeasurable.aemeasurable))

@[measurability]
theorem conj_q_lt_top'_aestrongly_measurable (g : Lp ℝ q μ)
    : AEStronglyMeasurable (conj_q_lt_top' g) μ := (aestronglyMeasurable_iff_aemeasurable (μ := μ)).mpr
  (conj_q_lt_top'_aemeasurable g)

theorem conj_q_lt_top'_of_ae_eq_zero (g : Lp ℝ q μ)
    (hg : g =ᵐ[μ] 0) (hq₁ : q > 1) (hqᵢ : q ≠ ∞) : conj_q_lt_top' g =ᵐ[μ] 0 := by
  apply ae_iff.mpr
  unfold conj_q_lt_top'
  simp_all
  apply measure_mono_null
  . show _ ⊆ {a | ¬g a = 0}; simp_all
  . exact ae_iff.mp hg

theorem conj_q_lt_top'_of_eq_zero (g : Lp ℝ q μ)
    (hg : g = 0) (hq₁ : q > 1) (hqᵢ : q ≠ ∞) : conj_q_lt_top' g =ᵐ[μ] 0 := by
  have : g =ᵐ[μ] 0 := eq_zero_iff_ae_eq_zero.mp hg
  exact conj_q_lt_top'_of_ae_eq_zero g this hq₁ hqᵢ

theorem conj_q_lt_top'_of_nnnorm_zero (g : Lp ℝ q μ)
    (hg : ‖g‖₊ = 0) (hq₁ : q > 1) (hqᵢ : q ≠ ∞) : conj_q_lt_top' ↑g =ᵐ[μ] 0 := by
  have : g = 0 := (nnnorm_eq_zero_iff q_gt_zero).mp hg
  exact conj_q_lt_top'_of_eq_zero g this hq₁ hqᵢ

@[simp]
theorem snorm'_of_conj_q_lt_top' (hqᵢ : q ≠ ∞) (g : Lp ℝ q μ)
    : snorm' (conj_q_lt_top' g) p.toReal μ
    = (snorm' g q.toReal μ) ^ (q.toReal - 1) := by
  unfold snorm'
  rw [←ENNReal.rpow_mul, ←q_div_p_add_one'' (q := q) (p := p) hqᵢ]
  rw [←mul_div_right_comm (a := 1) (c := q.toReal)]
  rw [one_mul, div_div, div_mul_cancel_right₀ (q_ne_zero' (p := p) hqᵢ) (a := p.toReal)]
  rw [inv_eq_one_div]
  congr 1

  unfold conj_q_lt_top'
  unfold ENNReal.rpow'

  conv =>
    lhs
    pattern _ ^ _
    rw [nnnorm_mul, ENNReal.coe_mul, (ENNReal.mul_rpow_of_nonneg _ _ p_ge_zero')]
    congr
    rfl
    rw [ENNReal.coe_rpow_of_nonneg _ p_ge_zero']
    congr
    rw [←Real.toNNReal_eq_nnnorm_of_nonneg toReal_nonneg]
    rw [toNNReal_eq_toNNreal_of_toReal, ENNReal.toNNReal_rpow]
    congr
    dsimp [ENNReal.rpow]
    rw [←ENNReal.rpow_mul]
    congr
    rfl
    rw [sub_mul (c := p.toReal), one_mul, mul_comm, ←p_add_q' hqᵢ]
    simp
    rfl

  conv =>
    lhs
    pattern _*_
    congr

    . rw [rpow_of_nnnorm_of_sign _ _ p_gt_zero']
      rfl

    . rw [ENNReal.coe_toNNReal]
      rfl
      apply ENNReal.rpow_of_to_ENNReal_of_NNReal_ne_top _ _ q_ge_zero'

  apply lintegral_congr_ae
  apply ae_iff.mpr
  simp_all

  conv =>
    lhs
    pattern _ ^ _
    rw [ENNReal.zero_rpow_of_pos (q_gt_zero' hqᵢ)]
    rfl

  simp

@[simp]
theorem snorm_of_conj_q_lt_top' (hqᵢ : q ≠ ∞) (g : Lp ℝ q μ)
    : snorm (conj_q_lt_top' g) p μ = (snorm g q μ) ^ (q.toReal - 1) := by
  rw [snorm_eq_snorm', snorm_eq_snorm']
  · exact _root_.trans (snorm'_of_conj_q_lt_top' (p := p) (q := q) (hqᵢ) g) rfl
  · exact q_ne_zero (p := p)
  · exact hqᵢ
  · exact p_ne_zero (q := q)
  · exact p_ne_top

theorem Memℒp_conj_q_lt_top' (hqᵢ : q ≠ ∞) (g : Lp ℝ q μ)  : Memℒp (conj_q_lt_top' g) p μ := by
  constructor
  . measurability
  . rw [snorm_of_conj_q_lt_top' hqᵢ g]
    exact ENNReal.rpow_lt_top_of_nonneg (q_sub_one_nneg' (p := p) hqᵢ) (snorm_ne_top g)

def conj_q_lt_top (hqᵢ : q ≠ ∞) (g : Lp ℝ q μ) : Lp ℝ p μ :=
  toLp (conj_q_lt_top' g) (Memℒp_conj_q_lt_top' hqᵢ g)

@[simp]
theorem snorm_of_conj_q_lt_top (hqᵢ : q ≠ ∞) (g : Lp ℝ q μ)
    : snorm (conj_q_lt_top (p := p) hqᵢ g) p μ = (snorm g q μ) ^ (q.toReal - 1) := by
  apply _root_.trans; show _ = snorm (conj_q_lt_top' g) p μ; swap
  · exact snorm_of_conj_q_lt_top' hqᵢ g
  · exact snorm_congr_ae (coeFn_toLp _ )

@[simp]
theorem norm_of_conj_q_lt_top (hqᵢ : q ≠ ∞) (g : Lp ℝ q μ)
    : ‖conj_q_lt_top (p := p) hqᵢ g‖ = ‖g‖ ^ (q.toReal - 1) := by
  rw [norm_def, norm_def, ENNReal.toReal_rpow]
  congr
  exact snorm_of_conj_q_lt_top (p := p) hqᵢ g

theorem int_conj_q_lt_top_mul_self (hqᵢ : q ≠ ∞) {g : Lp ℝ q μ}
    : ‖∫ (x : α), (conj_q_lt_top (p := p) hqᵢ g) x * g x ∂μ‖ = ‖g‖ := by
  sorry

end conj_q_lt_top'

section normalized_conj_q_lt_top'

def normalized_conj_q_lt_top' {q : ℝ≥0∞} (g : Lp ℝ q μ) : α → ℝ :=
  fun x => (conj_q_lt_top' g x) * (rpow' (1 - q.toReal) ‖g‖₊)

@[measurability]
theorem normalized_conj_q_lt_top'_ae_measurable (g : Lp ℝ q μ)
    : AEMeasurable (normalized_conj_q_lt_top' g) μ := by
  unfold normalized_conj_q_lt_top'
  exact AEMeasurable.mul_const (conj_q_lt_top'_aemeasurable g) _

@[measurability]
theorem normalized_conj_q_lt_top'_aestrongly_measurable (g : Lp ℝ q μ)
    : AEStronglyMeasurable (normalized_conj_q_lt_top' g) μ := by
  unfold normalized_conj_q_lt_top'
  exact (aestronglyMeasurable_iff_aemeasurable (μ := μ)).mpr (normalized_conj_q_lt_top'_ae_measurable g)

@[simp]
theorem snorm'_normalized_conj_q_lt_top' {g : Lp ℝ q μ} (hqᵢ : q ≠ ∞) (hg : ‖g‖₊ ≠ 0)
    : snorm' (normalized_conj_q_lt_top' g) p.toReal μ = 1 := by
  unfold normalized_conj_q_lt_top'
  rw [rpow', snorm'_mul_const p_gt_zero',
     snorm'_of_conj_q_lt_top' hqᵢ,
     NNReal.rpow_eq_pow,
     coe_rpow,
     coe_nnnorm,
     ←snorm_eq_snorm',
     norm_def,
     ←neg_sub q.toReal]
  case hp_ne_zero => exact q_ne_zero (p := p)
  case hp_ne_top => exact hqᵢ

  generalize hx : snorm g q μ = x
  generalize hy : q.toReal - 1 = y

  have y_pos : y > 0 := by
    calc _ = q.toReal - 1 := by rw [hy]
         _ > 1 - 1        := by gcongr; apply q_gt_one' (p := p) hqᵢ
         _ = 0            := by ring

  have y_nneg : y ≥ 0 := by linarith[y_pos]

  have x_ne_top : x ≠ ∞ := hx ▸ snorm_ne_top g

  have x_ne_zero : x ≠ 0 := by
    calc _ = snorm g q μ            := by rw [hx]
         _ = (snorm g q μ).toNNReal := by symm; apply ENNReal.coe_toNNReal; rw [hx]; exact x_ne_top
         _ = ‖g‖₊                   := by rw [nnnorm_def]
         _ ≠ 0                      := ENNReal.coe_ne_zero.mpr hg

  have x_rpow_y_ne_top : x^y ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg y_nneg x_ne_top

  rw [←ENNReal.coe_toNNReal (a := x ^ y) x_rpow_y_ne_top,
     ENNReal.toReal_rpow,
     ENNReal.nnnorm_of_toReal_eq_toNNReal]
  norm_cast
  rw [←ENNReal.toNNReal_mul,
     ←ENNReal.one_toNNReal]
  congr
  rw [←ENNReal.rpow_add]
  . simp
  . exact x_ne_zero
  . exact x_ne_top

@[simp]
theorem snorm_normalized_conj_q_lt_top' (hqᵢ : q ≠ ∞) {g : Lp ℝ q μ} (hg : ‖g‖₊ ≠ 0)
    : snorm (normalized_conj_q_lt_top' g) p μ = 1 := by
  rw [snorm_eq_snorm']
  · exact snorm'_normalized_conj_q_lt_top' hqᵢ hg
  · exact p_ne_zero (q := q)
  · exact p_ne_top (p := p)

theorem Memℒp_normalized_conj_q_lt_top' (hqᵢ : q ≠ ∞) {g : Lp ℝ q μ} (hg : ‖g‖₊ ≠ 0)
    : Memℒp (normalized_conj_q_lt_top' g) p μ := by
  constructor
  . exact normalized_conj_q_lt_top'_aestrongly_measurable g
  . rw [snorm_normalized_conj_q_lt_top' hqᵢ hg]
    trivial

def normalized_conj_q_lt_top (hqᵢ : q ≠ ∞) {g : Lp ℝ q μ} (hg : ‖g‖₊ ≠ 0) : Lp ℝ p μ :=
  toLp (normalized_conj_q_lt_top' g) (Memℒp_normalized_conj_q_lt_top' hqᵢ hg)

@[simp]
theorem snorm_normalized_conj_q_lt_top (hqᵢ : q ≠ ∞) {g : Lp ℝ q μ} (hg : ‖g‖₊ ≠ 0)
    : snorm (normalized_conj_q_lt_top (p := p) hqᵢ hg) p μ = 1 := by
  apply _root_.trans
  show _ = snorm (normalized_conj_q_lt_top' g) p μ;
  · exact snorm_congr_ae (coeFn_toLp _)
  · exact snorm_normalized_conj_q_lt_top' hqᵢ hg

@[simp]
theorem norm_of_normalized_conj_q_lt_top (hqᵢ : q ≠ ∞) {g : Lp ℝ q μ} (hg : ‖g‖₊ ≠ 0)
    : ‖normalized_conj_q_lt_top (p := p) hqᵢ hg‖ = 1 := by
  rw [norm_def, ←ENNReal.one_toReal]
  congr
  exact snorm_normalized_conj_q_lt_top (p := p) hqᵢ hg

theorem int_normalized_conj_q_lt_top_mul_self (hqᵢ : q ≠ ∞) {g : Lp ℝ q μ} (hg : ‖g‖₊ ≠ 0)
    : ‖∫ (x : α), (normalized_conj_q_lt_top (p := p) hqᵢ hg) x * g x ∂μ‖ = ‖g‖ := by
  sorry

end normalized_conj_q_lt_top'

theorem snorm_eq_sup_abs'' {μ : Measure α} (hμ : SigmaFinite μ) (g : Lp ℝ ∞ μ) :
    ‖g‖ = sSup ((fun f => ‖∫ x, (f x) * (g x) ∂μ‖) '' {(f : Lp ℝ 1 μ) | ‖f‖ ≤ 1}) := by
  -- we need μ to be σ-finite
  sorry

theorem snorm_eq_sup_q_gt_top (g : Lp ℝ q μ) (hqᵢ : q ≠ ∞) :
              ‖g‖ = sSup ((fun f => ‖∫ x, (f x) * (g x) ∂μ‖) '' {(f : Lp ℝ p μ) | ‖f‖ ≤ 1}) := by
  apply le_antisymm;
  . apply le_csSup
    . use ‖g‖
      intro x hx
      rcases hx with ⟨f, hf, rfl⟩
      dsimp at hf
      dsimp only
      calc _ ≤ ∫ x, ‖f x * g x‖ ∂μ             := norm_integral_le_integral_norm _
           _ = ∫ x, ‖(mul ℝ ℝ) (f x) (g x)‖ ∂μ := rfl
           _ ≤ ‖(mul ℝ ℝ)‖ * ‖f‖ * ‖g‖         := integral_mul_le _ hpq.out _
           _ = ‖f‖ * ‖g‖                       := by simp
           _ ≤ 1 * ‖g‖                         := by gcongr
           _ = ‖g‖                             := by simp
    . use normalized_conj_q_lt_top (p := p) hqᵢ (?_ : ‖g‖₊ ≠ 0)
      swap; sorry
      constructor
      . simp only [Set.mem_setOf_eq]
        rw [norm_of_normalized_conj_q_lt_top]
      . dsimp only
        exact int_normalized_conj_q_lt_top_mul_self (p := p) hqᵢ (?_ : ‖g‖₊ ≠ 0)

  . refine Real.sSup_le (fun x hx ↦ ?_) (norm_nonneg _)
    rcases hx with ⟨f, hf, rfl⟩
    simp at hf; dsimp only

    calc _ ≤ ∫ x, ‖f x * g x‖ ∂μ             := norm_integral_le_integral_norm _
         _ = ∫ x, ‖(mul ℝ ℝ) (f x) (g x)‖ ∂μ := by simp only [norm_mul, norm_eq_abs, mul_apply']
         _ ≤ ‖(mul ℝ ℝ)‖ * ‖f‖ * ‖g‖         := integral_mul_le _ hpq.out _
         _ = ‖f‖ * ‖g‖                       := by rw [opNorm_mul, one_mul]
         _ ≤ 1 * ‖g‖                         := by gcongr
         _ = ‖g‖                             := by rw [one_mul]

variable (p q μ) in
theorem snorm_eq_sup_abs (hμ : SigmaFinite μ) (g : Lp ℝ q μ):
              ‖g‖ = sSup ((fun f => ‖∫ x, (f x) * (g x) ∂μ‖) '' {(f : Lp ℝ p μ) | ‖f‖ ≤ 1}) := by

  by_cases hqᵢ : q ≠ ⊤; swap
  . simp at hqᵢ
    have hp₁ : p = 1 := by {
      rw [left_eq_one_iff, ← hqᵢ]
      exact hpq.out
    }
    subst hqᵢ; subst hp₁
    sorry
  . sorry

/- The map sending `g` to `f ↦ ∫ x, L (g x) (f x) ∂μ` induces a map on `L^q` into
`Lp E₂ p μ →L[ℝ] E₃`. Generally we will take `E₃ = ℝ`. -/
variable (p μ) in
def toDual (g : Lp E₁ q μ) : Lp E₂ p μ →L[ℝ] E₃ := by{

  let F : Lp E₂ p μ → E₃ := fun f ↦ ∫ x, L (g x) (f x) ∂μ

  have : IsBoundedLinearMap ℝ F := by{
    exact {
      map_add := by{
        intro f₁ f₂
        simp [F]
        rw [← integral_add]
        · apply integral_congr_ae
          filter_upwards [coeFn_add f₁ f₂] with a ha
          norm_cast
          rw [ha]
          simp
        · exact ENNReal.IsConjExponent.integrable_bilin L hpq.out.symm μ (Lp.memℒp g) (Lp.memℒp f₁)
        · exact ENNReal.IsConjExponent.integrable_bilin L hpq.out.symm μ (Lp.memℒp g) (Lp.memℒp f₂)
        }

      map_smul := by{
        intro m f
        simp [F]
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards [coeFn_smul m f] with a ha
        rw [ha]
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
    simp [toDual, IsBoundedLinearMap.toContinuousLinearMap, IsBoundedLinearMap.toLinearMap]
    ext f
    simp
    rw [← integral_add]
    · apply integral_congr_ae
      filter_upwards [coeFn_add g₁ g₂] with a ha
      norm_cast
      rw [ha]
      simp
    · exact ENNReal.IsConjExponent.integrable_bilin L' hpq.out.symm μ (Lp.memℒp g₁) (Lp.memℒp f)
    · exact ENNReal.IsConjExponent.integrable_bilin L' hpq.out.symm μ (Lp.memℒp g₂) (Lp.memℒp f)
  }
  map_smul':= by{
    intro m g
    simp [toDual, IsBoundedLinearMap.toContinuousLinearMap, IsBoundedLinearMap.toLinearMap]
    ext f
    simp
    rw [← integral_mul_left] -- mul vs smul
    apply integral_congr_ae
    filter_upwards [coeFn_smul m g] with a ha
    rw [ha]
    simp [L'mul]; ring
  }
  norm_map' := by {
    intro g
    conv_lhs => simp [Norm.norm]
    apply ContinuousLinearMap.opNorm_eq_of_bounds
    . simp
    . intro f
      calc ‖(toDual p μ L' g) f‖ ≤ ∫ x, ‖L' (g x) (f x)‖ ∂μ := by apply norm_integral_le_integral_norm
           _ ≤ ‖L'‖ * ‖g‖ * ‖f‖ := by apply integral_mul_le L' hpq.out.symm
           _ = ‖g‖ * ‖f‖ := by simp [L'norm_one]
           _ = _ := by aesop
    . intro N Nnneg
      intro hbound
      sorry
  }

/- The map sending `g` to `f ↦ ∫ x, L (f x) (g x) ∂μ` is a linear isometry. -/
variable (p q μ) in
def toDualₗᵢ : Lp E₁ q μ →ₗᵢ[ℝ] Lp E₂ p μ →L[ℝ] E₃ where

  toFun := toDual _ _ L
  map_add':= by{
    intro g₁ g₂
    simp [toDual, IsBoundedLinearMap.toContinuousLinearMap, IsBoundedLinearMap.toLinearMap]
    ext f
    simp
    rw [← integral_add]
    · apply integral_congr_ae
      filter_upwards [coeFn_add g₁ g₂] with a ha
      norm_cast
      rw [ha]
      simp
    · exact ENNReal.IsConjExponent.integrable_bilin L hpq.out.symm μ (Lp.memℒp g₁) (Lp.memℒp f)
    · exact ENNReal.IsConjExponent.integrable_bilin L hpq.out.symm μ (Lp.memℒp g₂) (Lp.memℒp f)
  }
  map_smul':= by{
    intro m g
    simp [toDual, IsBoundedLinearMap.toContinuousLinearMap, IsBoundedLinearMap.toLinearMap]
    ext f
    simp
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [coeFn_smul m g] with a ha
    rw [ha]
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
