import Mathlib.Analysis.Complex.AbsMax

noncomputable section

open NNReal ENNReal NormedSpace MeasureTheory Set Complex Bornology

variable {α β E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {n : MeasurableSpace β} {p q : ℝ≥0∞}
  {μ : Measure α} {ν : Measure β}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [FiniteDimensional ℂ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [FiniteDimensional ℂ E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℂ E₃] [FiniteDimensional ℂ E₃]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E₁] [BorelSpace E₁]
  [MeasurableSpace E₂] [BorelSpace E₂]
  [MeasurableSpace E₃] [BorelSpace E₃]
  {f : α → E} {t : ℝ}

/- The maximum modulus principle is the result below
(and that file also contains useful corollaries). -/
#check Complex.eqOn_of_isPreconnected_of_isMaxOn_norm


/-- Hadamard's three lines lemma/theorem on the unit strip with bounds M₀=M₁=1 and vanishing at infinity condition. -/
theorem DiffContOnCl.norm_le_pow_mul_pow''' {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f { z | z.re ∈ Ioo 0 1})
    (h2f : IsBounded (f '' { z | z.re ∈ Icc 0 1}))
    (h₀f : ∀ y : ℝ, ‖f (I * y)‖ ≤ 1) (h₁f : ∀ y : ℝ, ‖f (1 + I * y)‖ ≤ 1)
    {y t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) :
    ‖f (t + I * y)‖ ≤ 1 := by{
      -- MISSING HYPOTHESIS OF VANISHING AT INFINITY IN THE STATEMENT
      sorry
    }



/-- Hadamard's three lines lemma/theorem on the unit strip with bounds M₀=M₁=1. -/
theorem DiffContOnCl.norm_le_pow_mul_pow'' {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f { z | z.re ∈ Ioo 0 1})
    (h2f : IsBounded (f '' { z | z.re ∈ Icc 0 1}))
    (h₀f : ∀ y : ℝ, ‖f (I * y)‖ ≤ 1) (h₁f : ∀ y : ℝ, ‖f (1 + I * y)‖ ≤ 1)
    {y t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) :
    ‖f (t + I * y)‖ ≤ 1 := by{

      sorry
    }


/-- Hadamard's three lines lemma/theorem on the unit strip. -/
theorem DiffContOnCl.norm_le_pow_mul_pow₀₁ {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f { z | z.re ∈ Ioo 0 1})
    (h2f : IsBounded (f '' { z | z.re ∈ Icc 0 1}))
    {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀f : ∀ y : ℝ, ‖f (I * y)‖ ≤ M₀) (h₁f : ∀ y : ℝ, ‖f (1 + I * y)‖ ≤ M₁)
    {y t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) :
    ‖f (t + I * y)‖ ≤ M₀ ^ s * M₁ ^ t := by{
      let g:= fun z ↦ M₀ ^ (z-1) * M₁ ^(-z) * (f z)
      let p₁ : ℂ → ℂ := fun z ↦ M₀ ^ (z-1)
      let p₂ : ℂ → ℂ := fun z ↦ M₁ ^(-z)
      let h : ℂ → ℂ := fun z ↦ p₁ z • p₂ z
      have hsmul : g = fun z ↦ h z • f z := rfl
      have hg: DiffContOnCl ℂ g { z | z.re ∈ Ioo 0 1} := by {
        rw[hsmul]
        apply DiffContOnCl.smul
        · simp only [h]
          apply DiffContOnCl.smul
          · simp only [p₁]
            sorry
          · sorry
        · exact hf
      }
      have h2g:  IsBounded (g '' { z | z.re ∈ Icc 0 1}) := by sorry
      have h₀g : ∀ y : ℝ, ‖g (I * y)‖ ≤ 1 := by {
        intro y
        simp [g]
        have h₁ : Complex.abs (↑M₀ ^ (I * ↑y - 1)) = M₀⁻¹  := by{
          rw [Complex.abs_cpow_eq_rpow_re_of_pos hM₀]
          simp
          norm_cast
          simp
        }

        have h₂ : Complex.abs (↑M₁ ^ (-(I * ↑y))) = 1  := by{
          rw [Complex.abs_cpow_eq_rpow_re_of_pos hM₁]
          simp
        }

        rw[h₁, h₂]

        -- I highly doubt the following is the smartest way of doing it
        have : M₀⁻¹ = Ring.inverse M₀ := by simp
        have : 1 = M₀⁻¹ * M₀ := by {
          symm
          rw[this]
          apply Ring.inverse_mul_cancel M₀
          simp
          exact ne_of_gt hM₀
        }
        simp
        rw[this]
        gcongr
        exact h₀f y
      }

      --Essentially same proof as above with essentially the same code
      have h₁g: ∀ y : ℝ, ‖g (1 + I * y)‖ ≤ 1 := by {
        intro y
        simp [g]

        have h₁ : Complex.abs (↑M₀ ^ (I * ↑y)) = 1  := by{
          rw [Complex.abs_cpow_eq_rpow_re_of_pos hM₀]
          simp
        }

        have h₂ : Complex.abs (↑M₁ ^ (-(I * ↑y) + (- 1))) = M₁⁻¹  := by{
          rw [Complex.abs_cpow_eq_rpow_re_of_pos hM₁]
          simp
          norm_cast
          simp
        }

        rw[h₁, h₂]
        simp

        -- I highly doubt the following is the smartest way of doing it
        have : M₁⁻¹ = Ring.inverse M₁ := by simp
        have : 1 = M₁⁻¹ * M₁ := by {
          symm
          rw[this]
          apply Ring.inverse_mul_cancel M₁
          simp
          exact ne_of_gt hM₁
        }
        simp
        rw[this]
        gcongr
        exact h₁f y
      }

      have hgoal := DiffContOnCl.norm_le_pow_mul_pow'' hg h2g h₀g h₁g ht hs hts (y:=y)
      simp[g] at hgoal
      simp[hgoal]

      --This is also essentially the same thing I did before to prove the bounds, so yet more duplicate code
      have h₁: Complex.abs (↑M₀ ^ (↑t + I * ↑y - 1)) = M₀ ^ (t-1) := by{
        rw [Complex.abs_cpow_eq_rpow_re_of_pos hM₀]
        simp
      }

      have h₂: Complex.abs (↑M₁ ^ (-(I * ↑y) + -↑t)) = M₁ ^ (-t) := by{
        rw [Complex.abs_cpow_eq_rpow_re_of_pos hM₁]
        simp
      }

      rw[h₁, h₂] at hgoal
      --The rest is just very painful dealing with inequalities but it should be just manual labour

      sorry
    }



theorem DiffContOnCl.norm_le_pow_mul_pow {a b : ℝ} {f : ℂ → ℂ} (hab: a<b)
    (hf : DiffContOnCl ℂ f { z | z.re ∈ Ioo a b})
    (h2f : IsBounded (f '' { z | z.re ∈ Icc a b}))
    {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀f : ∀ y : ℝ, ‖f (a + I * y)‖ ≤ M₀) (h₁f : ∀ y : ℝ, ‖f (b + I * y)‖ ≤ M₁)
    {x y t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hx : x = t * a + s * b) (hts : t + s = 1) :
    ‖f (x + I * y)‖ ≤ M₀ ^ (1-((t-1)*a+s*b)/(b-a)) * M₁ ^ (((t-1)*a+s*b)/(b-a)) := by{

      have hts' : t = 1-s := by {
          symm
          rw[sub_eq_of_eq_add]
          exact hts.symm
        }

      have hts'' : s = 1-t := by {
        symm
        -- Not sure why this is so messed up if I don't make it explicit
        rw[@sub_eq_of_eq_add ℝ _ (1:ℝ) t s]
        rw[add_comm]
        exact hts.symm
      }

      have hax: x ≥ a := by{
        simp[hx]
        rw[hts']
        ring_nf
        have : -(s * a) + s * b = s * (b-a) := by ring
        rw[this]
        simp
        rw[mul_nonneg_iff]
        left
        constructor
        · exact hs
        · simp; exact le_of_lt hab
      }

      -- Essentially same as above with minor tweaks
      have hxb: b ≥ x := by{
        simp[hx]
        rw[hts'']
        ring_nf
        have : t * a - t * b = t * (a-b) := by ring
        rw[this]
        simp
        rw[mul_nonpos_iff]
        left
        constructor
        · exact ht
        · simp; exact le_of_lt hab
      }


      let g : ℂ → ℂ := fun z ↦ f (a + (z.re *(b-a)) + I*z.im)
      have hg: DiffContOnCl ℂ g { z | z.re ∈ Ioo 0 1} := by{
        -- I guess write g as f after the squeeze and then use composition of DiffContOnCl functions
        sorry
      }
      have h2g: IsBounded (g '' { z | z.re ∈ Icc 0 1}) := by{
        simp only [g]
        apply IsBounded.subset h2f
        intro z hz
        obtain ⟨w, hw₁, hw₂⟩ := hz
        simp
        use ↑a + ↑w.re * (↑b - ↑a) + I * ↑w.im
        simp
        simp at hw₁
        constructor
        · constructor
          · rw[mul_nonneg_iff]; left
            constructor
            · exact hw₁.1
            · simp; exact le_of_lt hab
          · calc
            a + w.re * (b-a) ≤ a + 1 * (b-a) := by gcongr; simp; exact le_of_lt hab; exact hw₁.2
            _ = b := by ring
        · exact hw₂
      }

      have h₀g : ∀ y : ℝ, ‖g (I * y)‖ ≤ M₀ := by{
        simp only [g]
        simp
        exact h₀f
      }

      have h₁g : ∀ y : ℝ, ‖g (1 + I * y)‖ ≤ M₁ := by{
        simp only [g]
        simp
        exact h₁f
      }

      let t':= (x-a)/(b-a)
      let s':= 1 - t'
      have ht' : 0 ≤ t' := by {
        simp only [t']
        rw[div_nonneg_iff]
        left
        constructor
        · simp[hax]
        · simp; exact le_of_lt hab
      }

      have hs' : 0 ≤ s' := by {
        simp only [s', t']
        simp
        rw [div_le_one]
        · simp[hxb]
        · simp[hab]
      }
      have hts' : t' + s' = 1 := by simp[s']

      have hgoal := DiffContOnCl.norm_le_pow_mul_pow₀₁ hg h2g hM₀ hM₁ h₀g h₁g ht' hs' hts' (y:=y)
      simp [g] at hgoal
      simp only[t'] at hgoal
      simp at hgoal
      have : @HMul.hMul ℂ ℂ ℂ instHMul ((↑x - ↑a) / (↑b - ↑a)) (↑b - ↑a)  = (↑x - ↑a) := by{
        rw[mul_comm_div, div_self]
        · ring
        · norm_cast; rw[← Ne]
          apply ne_of_gt
          simp; exact hab
      }

      simp[this] at hgoal


      have ht'₁: t'=((t - 1) * a + s * b)/(b-a) := by{
        simp only [t', hx]
        ring
      }
      simp only [s'] at hgoal
      rw[← ht'₁]
      assumption
    }



variable (E p q μ) in
/-- The additive subgroup of `α →ₘ[μ] E` consisting of the simple functions in both
`L^p` and `L^q`. This is denoted `U` in [Ian Tice]. -/
def Lp.simpleFunc2 : AddSubgroup (α →ₘ[μ] E) :=
  (Lp.simpleFunc E p μ).map (AddSubgroup.subtype _) ⊓
  (Lp.simpleFunc E q μ).map (AddSubgroup.subtype _)

/- to do: `f ∈ Lp.simpleFunc2 E p q μ` iff
`snorm f p μ < ∞ ∧ snorm f q μ < ∞ ∧ f is a simple function`. -/

/-- A normed operator `T` is bounded on `Lp.simpleFunc2 p₀ p₁ q` w.r.t. the `L^p₀`
where the codomain uses the `L^q` norm. -/
def SBoundedBy (T : (α →ₘ[μ] E₁) → β →ₘ[ν] E₂) (p₀ p₁ q : ℝ≥0∞) (C : ℝ) : Prop :=
  ∀ (f : α →ₘ[μ] E₁), f ∈ Lp.simpleFunc2 E₁ p₀ p₁ μ →
  snorm (T f) q ν ≤ ENNReal.ofReal C * snorm f p₀ μ

/-- Riesz-Thorin interpolation theorem -/
theorem exists_lnorm_le_of_subadditive_of_lbounded {p₀ p₁ q₀ q₁ : ℝ≥0∞} {M₀ M₁ : ℝ}
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hν : q₀ = ∞ → q₁ = ∞ → SigmaFinite ν)
    (T : Lp.simpleFunc2 E p q μ)
    (T : (α →ₘ[μ] E₁) →ₗ[ℂ] β →ₘ[ν] E₂)
    (h₀T : SBoundedBy T p₀ p₁ q₀ M₀)
    (h₁T : SBoundedBy T p₁ p₀ q₁ M₁)
    {θ η : ℝ≥0} (hθη : θ + η = 1)
    {p q : ℝ≥0∞} (hp : p⁻¹ = (1 - θ) / p₀ + θ / p₁) (hr : q⁻¹ = (1 - θ) / q₀ + θ / q₁)
    (f : α →ₘ[μ] E₁) (hf : f ∈ Lp.simpleFunc2 E₁ p₀ p₁ μ) :
    snorm (T f) q ν ≤ ENNReal.ofReal (M₀ ^ (η : ℝ) * M₁ ^ (θ : ℝ)) * snorm f p μ := sorry
