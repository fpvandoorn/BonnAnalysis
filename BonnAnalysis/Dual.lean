import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Analysis.NormedSpace.LinearIsometry
import Mathlib.MeasureTheory.Integral.Bochner

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

lemma induction
    (P : (p q : ℝ≥0∞) → (p.IsConjExponent q) → Prop)
    (nnreal : ∀ ⦃p q : ℝ≥0⦄, (h : p.IsConjExponent q) → P p q h.coe_ennreal)
    (one : P 1 ∞ one_top) (infty : P ∞ 1 top_one) {p q : ℝ≥0∞} (h : p.IsConjExponent q) :
    P p q h := by
  by_cases hq : q = ∞
  · simp_rw [h.left_eq_one_iff.mpr hq, hq, one]
  by_cases hp : p = ∞
  · simp_rw [hp, h.left_eq_top_iff.mp hp, infty]
  have := nnreal <| h.toNNReal hp hq
  simp_rw [ENNReal.coe_toNNReal hp, ENNReal.coe_toNNReal hq] at this
  exact this

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

lemma lintegral_mul_le_one_top (μ : Measure α) {f : α → E₁} {g : α → E₂}
    (hf : AEMeasurable f μ) : ∫⁻ a, ‖f a‖₊ * ‖g a‖₊ ∂μ ≤ snorm f 1 μ * snorm g ⊤ μ := by
    calc ∫⁻ a, ‖f a‖₊ * ‖g a‖₊ ∂μ ≤ ∫⁻ (a : α), ‖f a‖₊ * snormEssSup g μ ∂μ := MeasureTheory.lintegral_mono_ae (h := by
        rw [Filter.eventually_iff, ← Filter.exists_mem_subset_iff]
        use {a | ↑‖g a‖₊ ≤ snormEssSup g μ}
        rw [← Filter.eventually_iff]
        exact ⟨ae_le_snormEssSup, by simp; intro _ ha; apply ENNReal.mul_left_mono ha⟩)
    _ = snorm f 1 μ * snorm g ⊤ μ := by
      rw [lintegral_mul_const'' _ hf.ennnorm]
      simp [snorm, snorm']

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
  case one => exact lintegral_mul_le_one_top _ hf
  case infty =>
    calc
      ∫⁻ a, ‖f a‖₊ * ‖g a‖₊ ∂μ = ∫⁻ a, ‖g a‖₊ * ‖f a‖₊ ∂μ := by simp_rw [mul_comm]
    _ ≤ snorm f ⊤ μ * snorm g 1 μ := by rw [mul_comm]; exact lintegral_mul_le_one_top _ hg

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
        use (snorm (↑↑g) q μ).toReal
        constructor
        · sorry
        · intro f
          simp[F]
          -- Bound norm of integral with integral of norm and apply Hölder inequality
          sorry
      }
    }
  }
  apply IsBoundedLinearMap.toContinuousLinearMap this
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
