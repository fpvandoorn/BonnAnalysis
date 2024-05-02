import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Analysis.NormedSpace.LinearIsometry
import Mathlib.MeasureTheory.Integral.Bochner

/-! We show that the dual space of `L^p` for `1 ≤ p < ∞`.

See [Stein-Shakarchi, Functional Analysis, section 1.4] -/
noncomputable section

open Real NNReal ENNReal NormedSpace MeasureTheory

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

namespace ENNReal

/-- Two numbers `p, q : ℝ≥0∞` are conjugate if `p⁻¹ + q⁻¹ = 1`.
This does allow for the case where one of them is `∞` and the other one is `1`,
in contrast to `NNReal.IsConjExponent`. -/
structure IsConjExponent (p q : ℝ≥0∞) : Prop where
  inv_add_inv_conj : p⁻¹ + q⁻¹ = 1

namespace IsConjExponent

lemma one_le_left (hpq : p.IsConjExponent q) : 1 ≤ p := sorry

lemma symm (hpq : p.IsConjExponent q) : q.IsConjExponent p := sorry

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

variable
  [hpq : Fact (p.IsConjExponent q)] [h'p : Fact (p < ∞)]
  [hp : Fact (1 ≤ p)] [hq : Fact (1 ≤ q)] -- note: these are superfluous, but it's tricky to make them instances.



--FROM MATHLIB
example (f g h : Lp E p μ) : (f + g) + h = f + (g + h) := by
  ext1
  filter_upwards [coeFn_add (f + g) h, coeFn_add f g, coeFn_add f (g + h), coeFn_add g h]
    with _ ha1 ha2 ha3 ha4
  simp only [ha1, ha2, ha3, ha4, add_assoc]



/- The map sending `g` to `f ↦ ∫ x, L (g x) (f x) ∂μ` induces a map on `L^q` into
`Lp E₂ p μ →L[ℝ] E₃`. Generally we will take `E₃ = ℝ`. -/
variable (p μ) in
def toDual (g : Lp E₁ q μ) : Lp E₂ p μ →L[ℝ] E₃ where
  toFun := fun f ↦ ∫ x, L (g x) (f x) ∂μ
  map_add' := by{
    /-The subtle part of this proof is that [f+g] = [f] + [g] in L^p. This is actually already in Mathlib.-/
    intro f₁ f₂
    simp
    have : (fun x ↦ (L (g x)) ((f₁ + f₂) x)) =ᵐ[μ]  fun x ↦ (L (g x)) (f₁ x + f₂ x) := by sorry
    have : ∫ (x : α), (L (g x)) ((f₁ + f₂) x) ∂μ = ∫ (x : α), (L (g x)) (f₁ x + f₂ x) ∂μ := by sorry
    simp at this
    rw[this, integral_add]
    · exact ENNReal.IsConjExponent.integrable_bilin L μ (Lp.memℒp g) (Lp.memℒp f₁)
    · exact ENNReal.IsConjExponent.integrable_bilin L μ (Lp.memℒp g) (Lp.memℒp f₂)
  }
  map_smul' := by{
    intro m f
    simp
    rw[← integral_smul]
    apply integral_congr_ae
    have : (fun a ↦ (L (g a)) ((m • f) a)) =ᵐ[μ] ↑(AEEqFun.comp₂ L _ g (m • f)) := by{
      -- why is this breaking down? I'm confused
      apply MeasureTheory.AEEqFun.coeFn_comp₂
    }


    rw [← MeasureTheory.AEEqFun.coeFn_comp₂]
    apply MeasureTheory.AEEqFun.coeFn_smul
    sorry
    --rw[← MeasureTheory.AEEqFun.ext_iff]



  }
  cont := by {
    apply IsBoundedLinearMap.toContinuousLinearMap
    simp
    -- prove bounded + Hölder inequality (adapt lintegral_mul_le)
  }

#check MeasureTheory.AEEqFun.coeFn_comp₂
#check MeasureTheory.AEEqFun.coeFn_comp₂Measurable
#check MeasureTheory.AEEqFun.coeFn_smul
#check integral_congr_ae

/- The map sending `g` to `f ↦ ∫ x, L (f x) (g x) ∂μ` is a linear isometry. -/
variable (p q μ) in
def toDualₗᵢ : Lp E₁ q μ →ₗᵢ[ℝ] Lp E₂ p μ →L[ℝ] E₃ where
  toFun := toDual _ _ L
  map_add':= sorry
  map_smul':= sorry
  norm_map' := by {
    intro f
    simp
    sorry
  }

/- The map sending `g` to `f ↦ ∫ x, L (f x) (g x) ∂μ` is a linear isometric equivalence.  -/
variable (p q μ) in
def dualIsometry (L : E₁ →L[ℝ] Dual ℝ E₂) :
    Dual ℝ (Lp E₂ p μ) ≃ₗᵢ[ℝ] Lp E q μ :=
  sorry

end Lp
end MeasureTheory
