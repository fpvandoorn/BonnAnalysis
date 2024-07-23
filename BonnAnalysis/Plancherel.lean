import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import BonnAnalysis.StrongType

noncomputable section

open FourierTransform MeasureTheory Real

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V]

/-- Part of **Plancherel theorem**: if `f` is in `L¹ ∩ L²` then its Fourier transform is also in
`L²`. -/
theorem memℒp_fourierIntegral {f : V → E} (hf : Integrable f) (h2f : Memℒp f 2) :
    Memℒp (𝓕 f) 2 := sorry

/-- Part of **Plancherel theorem**: if `f` is in `L¹ ∩ L²` then its inverse Fourier transform is
also in `L²`. -/
theorem memℒp_fourierIntegralInv {f : V → E} (hf : Integrable f) (h2f : Memℒp f 2) :
    Memℒp (𝓕⁻ f) 2 := sorry

/-- **Plancherel theorem**: if `f` is in `L¹ ∩ L²` then its Fourier transform has the same
`L²` norm as that of `f`. -/
theorem snorm_fourierIntegral {f : V → E} (hf : Integrable f) (h2f : Memℒp f 2) :
    snorm (𝓕 f) 2 volume = snorm f 2 volume := sorry

/-- **Plancherel theorem**: if `f` is in `L¹ ∩ L²` then its inverse Fourier transform has the same
`L²` norm as that of `f`. -/
theorem snorm_fourierIntegralInv {f : V → E} (hf : Integrable f) (h2f : Memℒp f 2) :
    snorm (𝓕⁻ f) 2 volume = snorm f 2 volume := sorry


scoped[MeasureTheory] notation:25 α " →₁₂[" μ "] " E =>
    ((α →₁[μ] E) ⊓ (α →₂[μ] E) : AddSubgroup (α →ₘ[μ] E))

/- Note: `AddSubgroup.normedAddCommGroup` is almost this, but not quite. -/
instance : NormedAddCommGroup (V →₁₂[volume] E) :=
  AddGroupNorm.toNormedAddCommGroup {
    toFun := fun ⟨f,_⟩ ↦ ENNReal.toReal <| snorm f 2 volume
    map_zero' := by simp [snorm_congr_ae AEEqFun.coeFn_zero, snorm_zero]
    add_le' := fun ⟨f, _, hf⟩ ⟨g, _, hg⟩ ↦ ENNReal.toReal_le_add (by
        simp [snorm_congr_ae (AEEqFun.coeFn_add f g),
              snorm_add_le ((Lp.mem_Lp_iff_memℒp.1 hf).1) ((Lp.mem_Lp_iff_memℒp.1 hg).1)])
      ((Lp.mem_Lp_iff_snorm_lt_top.1 hf).ne) ((Lp.mem_Lp_iff_snorm_lt_top.1 hg).ne)
    neg' := by simp [snorm_congr_ae (AEEqFun.coeFn_neg _)]
    eq_zero_of_map_eq_zero' := by
      intro ⟨f, _, hf⟩ h
      simp [ENNReal.toReal_eq_zero_iff] at h
      rcases h with h | h; swap
      · absurd h; exact (Lp.mem_Lp_iff_snorm_lt_top.1 hf).ne
      ext
      apply ae_eq_trans <| (snorm_eq_zero_iff ((Lp.mem_Lp_iff_memℒp.1 hf).1) (by simp)).1 h
      apply ae_eq_trans (Lp.coeFn_zero E 2 volume).symm; rfl
  }

instance : NormedSpace ℝ (V →₁₂[volume] E) := sorry


/- The Fourier integral as a continuous linear map `L^1(V, E) ∩ L^2(V, E) → L^2(V, E)`. -/
def fourierIntegralL2OfL12Fun : (V →₁₂[volume] E) → (V →₂[volume] E) :=
  fun ⟨f,hf,hf2⟩ ↦ (memℒp_fourierIntegral (memℒp_one_iff_integrable.1 <|
      Lp.mem_Lp_iff_memℒp.1 hf) (Lp.mem_Lp_iff_memℒp.1 hf2)).toLp <| 𝓕 f

def fourierIntegralL2OfL12 : (V →₁₂[volume] E) →L[ℝ] (V →₂[volume] E) := sorry
  /-have : IsBoundedLinearMap ℝ fourierIntegralL2OfL12Fun := {
    map_add := sorry
    map_smul := sorry
    bound := sorry
  }
  IsBoundedLinearMap.toContinuousLinearMap this-/



/- The Fourier integral as a continuous linear map `L^2(V, E) → L^2(V, E)`. -/
def fourierIntegralL2 : (V →₂[volume] E) →L[ℝ] (V →₂[volume] E) :=
  sorry

end MeasureTheory
