import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Order.Filter.Basic
import BonnAnalysis.Dual

noncomputable section

open NNReal ENNReal NormedSpace MeasureTheory Set Complex Bornology Filter

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

/- TODO: split proofs into smaller lemmas to recycle code -/

-- All these names are probably very bad
lemma Real.rpow_le_rpow_iff_left {M:ℝ} (hM: M>0) (a b : ℝ) : M^a ≤ M^b ↔ ((1 ≤ M ∧ a ≤ b ) ∨ (M ≤ 1 ∧ b ≤ a)) := by{
  have hMb : M^(-b) > 0 := Real.rpow_pos_of_pos hM (-b)
  rw [← mul_le_mul_right hMb, ←Real.rpow_add hM, ← Real.rpow_add hM, add_right_neg, Real.rpow_zero,
    Real.rpow_le_one_iff_of_pos hM]
  simp
}


lemma pow_bound₀ {M:ℝ} (hM: M > 0) {z: ℂ} (hz: z.re ∈ Icc 0 1) : Complex.abs (M^(z-1)) ≤ max 1 (1/M) := by{
  rw[Complex.abs_cpow_eq_rpow_re_of_pos hM (z-1)]
  simp
  simp at hz
  by_cases h: M ≥ 1
  · left
    have : 1 = M^0 := rfl
    nth_rewrite 2 [this]
    have := (Real.rpow_le_rpow_iff_left hM (z.re-1) 0).mpr
    simp at this
    apply this
    left
    constructor
    · exact h
    · simp[hz.2]
  · right
    have : M^(-1:ℝ) = M⁻¹ := by apply Real.rpow_neg_one
    rw[← this]
    have := (Real.rpow_le_rpow_iff_left hM (z.re-1) (-1:ℝ)).mpr
    simp at this
    apply this
    right
    constructor
    · simp at h; exact le_of_lt h
    · exact hz.1
}

-- very similar proof to the previous one
lemma pow_bound₁ {M:ℝ} (hM: M > 0) {z: ℂ} (hz: z.re ∈ Icc 0 1) : Complex.abs (M^(-z)) ≤ max 1 (1/M) := by{
  rw[Complex.abs_cpow_eq_rpow_re_of_pos hM (-z)]
  simp
  simp at hz
  by_cases h: M ≥ 1
  · left
    have : 1 = M^0 := rfl
    rw [this]
    have := (Real.rpow_le_rpow_iff_left hM (-z.re) 0).mpr
    simp at this
    apply this
    left
    constructor
    · exact h
    · simp[hz.1]
  · right
    have : M^(-1:ℝ) = M⁻¹ := by apply Real.rpow_neg_one
    rw[← this]
    have := (Real.rpow_le_rpow_iff_left hM (-z.re) (-1:ℝ)).mpr
    simp at this
    apply this
    right
    constructor
    · simp at h; exact le_of_lt h
    · exact hz.2
}

/-I think both these definitions and the corresponding hypotheses htop and hbot in the theorem are quite clunky to work with but I couldn't do any better-/

def at_height (f:ℂ → ℂ) (y:ℝ) : (Icc 0 1 : Set ℝ) → ℝ  := fun x ↦ Complex.abs (f (x+ I*y))

def sup_at_height (f: ℂ → ℂ) (y: ℝ) := sSup ((at_height f y)'' univ)


/-- Hadamard's three lines lemma/theorem on the unit strip with bounds M₀=M₁=1 and vanishing at infinity condition. -/
theorem DiffContOnCl.norm_le_pow_mul_pow''' {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f { z | z.re ∈ Ioo 0 1})
    (h2f : IsBounded (f '' { z | z.re ∈ Icc 0 1}))
    (h₀f : ∀ y : ℝ, ‖f (I * y)‖ ≤ 1) (h₁f : ∀ y : ℝ, ‖f (1 + I * y)‖ ≤ 1)
    {y t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) (htop: Tendsto (fun y ↦ (sup_at_height f y)) atTop (nhds  0)) (hbot: Tendsto (fun y ↦ (sup_at_height f y)) atBot (nhds 0) ) :
    ‖f (t + I * y)‖ ≤ 1 := by{
      sorry
    }



/-Next goal: prove the three lines lemma with bounds M₀=M₁=1 -/

def bump (ε: ℝ) : ℂ → ℂ := fun z ↦ exp (ε * (z^2 -1))

lemma bump_diffcontoncl (ε : ℝ) : DiffContOnCl ℂ (bump ε) { z | z.re ∈ Ioo 0 1} := by{
  refine Differentiable.diffContOnCl ?h
  have h' : bump ε =  exp ∘ (fun z ↦ ε * (z^2 -1) ) := rfl
  rw[h']
  apply Differentiable.comp
  · exact differentiable_exp
  · simp
}

def perturb (f: ℂ → ℂ) (ε : ℝ) : ℂ → ℂ := fun z ↦ (f z) • (bump ε z)

lemma perturb_diffcontoncl {f: ℂ → ℂ} (hf : DiffContOnCl ℂ f { z | z.re ∈ Ioo 0 1}) (ε : ℝ) : DiffContOnCl ℂ (perturb f ε) { z | z.re ∈ Ioo 0 1} := by{
  apply DiffContOnCl.smul
  · exact hf
  · exact bump_diffcontoncl ε
}


lemma perturb_bound (f: ℂ → ℂ) (ε : ℝ) (z : ℂ) : Complex.abs (perturb f ε z) ≤ Complex.abs (f z) * Real.exp (ε * ((z.re)^2 - 1 - (z.im)^2)) := by{
  simp[perturb, bump]
  gcongr
  nth_rewrite 1 [Complex.abs_exp, ← Complex.re_add_im z,  add_sq']
  simp
  apply le_of_eq
  simp
  left
  norm_cast
  rw[mul_pow, Complex.I_sq]
  simp
  norm_cast
  ring
}

lemma bound_factor_le_one {ε : ℝ} (hε: ε > 0) {z : ℂ} (hz: z.re ∈ Icc 0 1) : Real.exp (ε * ((z.re)^2 - 1 - (z.im)^2)) ≤ 1 := by{
  simp at hz
  rw[Real.exp_le_one_iff]
  rw[mul_nonpos_iff]
  left
  constructor
  · exact le_of_lt hε
  · calc
    z.re ^ 2 - 1 - z.im ^ 2 ≤  z.re ^ 2 - 1 := by{ simp; exact sq_nonneg z.im}
    _ ≤ 0 := by {
      simp
      rw[abs_le]
      constructor
      · calc
        -1 ≤ 0 := by norm_num
        _ ≤ z.re := hz.1
      · exact hz.2
    }
}


lemma perturb_isbounded {f: ℂ → ℂ} (h2f : IsBounded (f '' { z | z.re ∈ Icc 0 1})) {ε : ℝ} (hε: ε>0) : IsBounded ((perturb f ε) '' { z | z.re ∈ Icc 0 1}) := by{
  apply (Metric.isBounded_iff_subset_ball 0).mpr
  obtain ⟨R, hR⟩:= (Metric.isBounded_iff_subset_ball 0).mp h2f
  simp only [subset_def, mem_image] at hR
  use R
  intro x hx
  simp at hx
  obtain ⟨z, hz₁, hz₂⟩ := hx
  rw[← hz₂]
  specialize hR (f z) (by use z; simp; exact hz₁)
  simp at hR
  have : R ≥ 0 := by{
    calc
    0 ≤ Complex.abs (f z) := by exact AbsoluteValue.nonneg Complex.abs (f z)
    _ ≤  R := le_of_lt hR
  }
  simp
  calc
  Complex.abs (perturb f ε z) ≤ Complex.abs (f z) * Real.exp (ε * ((z.re)^2 - 1 - (z.im)^2)) := perturb_bound f ε z
  _ < R * Real.exp (ε * ((z.re)^2 - 1 - (z.im)^2)) := by gcongr
  _ ≤ R * 1 := by gcongr; apply bound_factor_le_one hε; simp; exact hz₁
  _ ≤ R := by simp
}

-- This can probably be made shorter by using bound_factor_le_one
lemma perturb_bound_left {f: ℂ → ℂ} (h₀f : ∀ y : ℝ, ‖f (I * y)‖ ≤ 1) {ε : ℝ} (hε: ε > 0) (y: ℝ) : Complex.abs (perturb f ε (I*y)) ≤ 1 := by{
  have hb := perturb_bound f ε (I*y)
  simp at hb
  have : (ε * (-1 - y ^ 2)).exp ≤ 1 := by{
    rw[Real.exp_le_one_iff]
    rw[mul_nonpos_iff]
    left
    constructor
    · exact le_of_lt hε
    · simp
      calc
      -1 ≤ 0 := by norm_num
      _ ≤ y^2 := sq_nonneg y
  }
  calc
  Complex.abs (perturb f ε (I * ↑y)) ≤ Complex.abs (f (I * ↑y)) * (ε * (-1 - y ^ 2)).exp := hb
  _ ≤ Complex.abs (f (I * ↑y)) * 1 := by gcongr
  _ ≤ 1 := by simp; exact h₀f y
}

-- This can probably be made shorter by using bound_factor_le_one
lemma perturb_bound_right {f: ℂ → ℂ} (h₁f : ∀ y : ℝ, ‖f (1 + I * y)‖ ≤ 1) {ε : ℝ} (hε: ε>0) (y: ℝ) : Complex.abs (perturb f ε (1 + I*y)) ≤ 1 := by{
  have hb := perturb_bound f ε (1 + I*y)
  simp at hb

  have : (-(ε * y ^ 2)).exp ≤ 1 := by{
    rw[Real.exp_le_one_iff]
    simp
    rw[mul_nonneg_iff]
    left
    constructor
    · exact le_of_lt hε
    · exact sq_nonneg y
  }
  calc
  Complex.abs (perturb f ε (1 + I * ↑y)) ≤ Complex.abs (f (1 + I * ↑y)) * (-(ε * y ^ 2)).exp := hb
  _ ≤ Complex.abs (f (1 + I * ↑y)) * 1 := by gcongr
  _ ≤ 1 := by simp; exact h₁f y
}

--This is very ugly with nested calcs
lemma perturb_vanish_infty_down {f:ℂ → ℂ} (h2f : IsBounded (f '' { z | z.re ∈ Icc 0 1})) {ε : ℝ} (hε: ε > 0) :Tendsto (fun y ↦ sup_at_height (perturb f ε) y) atBot (nhds 0) := by{
  rw [tendsto_order]
  constructor
  · intro t ht
    filter_upwards
    intro y
    simp[sup_at_height]
    calc
    t < 0 := ht
    _ ≤ sSup (range (at_height (perturb f ε) y)) := by{
      apply Real.sSup_nonneg
      intro x hx
      simp[at_height, perturb] at hx
      obtain ⟨a, ha₁, ha₂, ha₃⟩:= hx
      positivity
    }
  · intro t ht
    simp[sup_at_height, at_height]
    obtain ⟨R, hR⟩:= (Metric.isBounded_iff_subset_ball 0).mp h2f
    simp only [subset_def, mem_image] at hR
    use - Real.sqrt ((Real.log R - Real.log (t/2))/ε)
    intro y hy
    calc
    sSup (range fun (a: (Icc 0 1 : Set ℝ)) ↦ Complex.abs (perturb f ε (↑↑a + I * ↑y))) ≤ t/2 := by{
      apply Real.sSup_le
      · intro x hx
        simp at hx
        obtain ⟨a, h₁a, h₂a, h₃a⟩ := hx
        specialize hR (f (a + I*y)) (by use a+I*y; constructor; simp; exact h₁a; rfl)
        simp at hR
        have hRpos : 0 < R := by{
          calc
          0 ≤ Complex.abs (f (↑a + I * ↑y)) := by apply AbsoluteValue.nonneg
          _ < R := hR
        }

        have hbump:= perturb_bound f ε (a+I*y)
        simp at hbump
        /-
        have : (ε * (a ^ 2 - 1 - y ^ 2)).exp ≤ (ε * (a^2 - 1)).exp := by{
          simp[hε]
          exact sq_nonneg y
        } -/
        have hyneg : 0 ≥  y := by{
          calc
          0 ≥ - √((R.log - (t / 2).log) / ε) := by simp; exact Real.sqrt_nonneg ((R.log - (t / 2).log) / ε)
          _ ≥  y := hy
        }

        have hy' : -y^2 ≤ - ((R.log - (t / 2).log) / ε) := by {
          simp
          rw[← Real.sqrt_le_sqrt_iff]
          · rw[Real.sqrt_sq_eq_abs, abs_of_nonpos hyneg, ← neg_le_neg_iff]; simp; exact hy
          · positivity
        }

        have hε' : ε ≠ 0 := by apply ne_of_gt; exact hε

        have hy'ε : ε * -y ^ 2 ≤ - ε * ((R.log - (t / 2).log) / ε) := by{
          simp
          simp at hy'
          rw[mul_le_mul_left hε]
          exact hy'
        }

        apply le_of_lt
        calc
        Complex.abs (perturb f ε (↑a + I * ↑y)) ≤ Complex.abs (f (↑a + I * ↑y)) * (ε * (a ^ 2 - 1 - y ^ 2)).exp := hbump
        _ < R * (ε * (a ^ 2 - 1 - y ^ 2)).exp := by gcongr
        _ ≤ t/2 := by{
          rw[← Real.log_le_log_iff, Real.log_mul, Real.log_exp]
          · calc
            R.log + ε * (a ^ 2 - 1 - y ^ 2) ≤ R.log + ε * (- y^2) := by{
              gcongr
              simp
              rw[abs_le]
              simp[h₁a]
              calc
              -1 ≤ 0 := by norm_num
              _ ≤ a := h₁a.1
            }
            _ ≤ R.log - ε * ((R.log - (t / 2).log) / ε) := by {
              have : R.log - ε * ((R.log - (t / 2).log) / ε) = R.log + (- ε * ((R.log - (t / 2).log) / ε)):= by ring
              rw[this]
              gcongr
            }
            _ ≤ (t/2).log := by {
              rw[mul_div_left_comm, div_self hε']
              simp
            }
          · exact ne_of_gt hRpos
          · exact Real.exp_ne_zero (ε * (a ^ 2 - 1 - y ^ 2))
          · positivity
          · positivity
        }
      · apply le_of_lt
        simp
        exact ht
    }
    _ < t := by norm_num; exact ht
}

--Almost the exact same (ugly) proof as above
lemma perturb_vanish_infty_up {f:ℂ → ℂ} (h2f : IsBounded (f '' { z | z.re ∈ Icc 0 1})) {ε : ℝ} (hε: ε > 0) :Tendsto (fun y ↦ sup_at_height (perturb f ε) y) atTop (nhds 0) := by{
  rw [tendsto_order]
  constructor
  · intro t ht
    filter_upwards
    intro y
    simp[sup_at_height]
    calc
    t < 0 := ht
    _ ≤ sSup (range (at_height (perturb f ε) y)) := by{
      apply Real.sSup_nonneg
      intro x hx
      simp[at_height, perturb] at hx
      obtain ⟨a, ha₁, ha₂, ha₃⟩:= hx
      positivity
    }

  · intro t ht
    simp[sup_at_height, at_height]
    obtain ⟨R, hR⟩:= (Metric.isBounded_iff_subset_ball 0).mp h2f
    simp only [subset_def, mem_image] at hR
    use Real.sqrt ((Real.log R - Real.log (t/2))/ε)
    intro y hy
    calc
    sSup (range fun (a: (Icc 0 1 : Set ℝ)) ↦ Complex.abs (perturb f ε (↑↑a + I * ↑y))) ≤ t/2 := by{
      apply Real.sSup_le
      · intro x hx
        simp at hx
        obtain ⟨a, h₁a, h₂a, h₃a⟩ := hx
        specialize hR (f (a + I*y)) (by use a+I*y; constructor; simp; exact h₁a; rfl)
        simp at hR
        have hRpos : 0 < R := by{
          calc
          0 ≤ Complex.abs (f (↑a + I * ↑y)) := by apply AbsoluteValue.nonneg
          _ < R := hR
        }

        have hbump:= perturb_bound f ε (a+I*y)
        simp at hbump
        /-
        have : (ε * (a ^ 2 - 1 - y ^ 2)).exp ≤ (ε * (a^2 - 1)).exp := by{
          simp[hε]
          exact sq_nonneg y
        } -/
        have hypos : 0 ≤ y := by{
          calc
          0 ≤ √((R.log - (t / 2).log) / ε) := Real.sqrt_nonneg ((R.log - (t / 2).log) / ε)
          _ ≤ y := hy
        }

        have hy' : -y^2 ≤ - ((R.log - (t / 2).log) / ε) := by {
          simp
          rw[← Real.sqrt_le_sqrt_iff]
          · rw[Real.sqrt_sq hypos]; exact hy
          · positivity
        }

        have hε' : ε ≠ 0 := by apply ne_of_gt; exact hε

        have hy'ε : ε * -y ^ 2 ≤ - ε * ((R.log - (t / 2).log) / ε) := by{
          simp
          simp at hy'
          rw[mul_le_mul_left hε]
          exact hy'
        }

        apply le_of_lt
        calc
        Complex.abs (perturb f ε (↑a + I * ↑y)) ≤ Complex.abs (f (↑a + I * ↑y)) * (ε * (a ^ 2 - 1 - y ^ 2)).exp := hbump
        _ < R * (ε * (a ^ 2 - 1 - y ^ 2)).exp := by gcongr
        _ ≤ t/2 := by{
          rw[← Real.log_le_log_iff, Real.log_mul, Real.log_exp]
          · calc
            R.log + ε * (a ^ 2 - 1 - y ^ 2) ≤ R.log + ε * (- y^2) := by{
              gcongr
              simp
              rw[abs_le]
              simp[h₁a]
              calc
              -1 ≤ 0 := by norm_num
              _ ≤ a := h₁a.1
            }
            _ ≤ R.log - ε * ((R.log - (t / 2).log) / ε) := by {
              have : R.log - ε * ((R.log - (t / 2).log) / ε) = R.log + (- ε * ((R.log - (t / 2).log) / ε)):= by ring
              rw[this]
              gcongr
            }
            _ ≤ (t/2).log := by {
              rw[mul_div_left_comm, div_self hε']
              simp
            }
          · exact ne_of_gt hRpos
          · exact Real.exp_ne_zero (ε * (a ^ 2 - 1 - y ^ 2))
          · positivity
          · positivity
        }
      · apply le_of_lt
        simp
        exact ht
    }
    _ < t := by norm_num; exact ht
}


lemma perturb_bound_strip {f : ℂ → ℂ} {ε : ℝ} (hε: ε > 0)
    (hf : DiffContOnCl ℂ f { z | z.re ∈ Ioo 0 1})
    (h2f : IsBounded (f '' { z | z.re ∈ Icc 0 1}))
    (h₀f : ∀ y : ℝ, ‖f (I * y)‖ ≤ 1) (h₁f : ∀ y : ℝ, ‖f (1 + I * y)‖ ≤ 1)
    {y t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) : ‖perturb f ε (t + I*y)‖ ≤ 1 := by {
      apply DiffContOnCl.norm_le_pow_mul_pow''' ?_ ?_ ?_ ?_ ht hs hts ?_ ?_
      · exact perturb_diffcontoncl hf ε
      · exact perturb_isbounded h2f hε
      · exact perturb_bound_left h₀f hε
      · exact perturb_bound_right h₁f hε
      · exact perturb_vanish_infty_up h2f hε
      · exact perturb_vanish_infty_down h2f hε
    }


lemma perturb_pointwise_converge {f : ℂ → ℂ} (z: ℂ) : Tendsto (fun ε ↦ perturb f ε z) (nhds 0) (nhds (f z)) := by{
  simp[perturb]
  have : (fun ε ↦ f z * bump ε z) = fun ε ↦ (((fun t ↦ f z) ε)  * ((fun t ↦ bump t z) ε)) := rfl
  rw[this]
  have : f z = f z * 1 := by simp
  nth_rewrite 2 [this]
  apply Filter.Tendsto.mul
  · exact tendsto_const_nhds
  · have : bump 0 z = 1 := by simp[bump]
    rw[← this]
    apply Continuous.tendsto (x:=0)
    simp[bump]
    have : (fun (x:ℝ) ↦ cexp (↑x * (z ^ 2 - 1))) = cexp ∘ (fun x ↦ x * (z^2 - 1)) ∘ (fun (x:ℝ) ↦ (x:ℂ)) := rfl
    rw[this]
    apply Continuous.comp
    · exact continuous_exp
    · apply Continuous.comp
      · exact continuous_mul_right (z ^ 2 - 1)
      · exact Complex.continuous_ofReal
}


lemma perturb_pointwise_norm_converge (f : ℂ → ℂ) (z: ℂ) : Tendsto (fun ε ↦ Complex.abs (perturb f ε z)) (nhdsWithin 0 (Ioi 0)) (nhds (Complex.abs (f z))) := by{
  have : (fun ε ↦ Complex.abs (perturb f ε z)) = Complex.abs ∘ (fun ε ↦ perturb f ε z) := rfl
  rw[this]
  apply Tendsto.comp (y:= nhds (f z))
  · apply Continuous.tendsto
    exact Complex.continuous_abs
  · apply Filter.Tendsto.mono_left (perturb_pointwise_converge z)
    apply nhdsWithin_le_nhds
}

/-- Hadamard's three lines lemma/theorem on the unit strip with bounds M₀=M₁=1. -/
theorem DiffContOnCl.norm_le_pow_mul_pow'' {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f { z | z.re ∈ Ioo 0 1})
    (h2f : IsBounded (f '' { z | z.re ∈ Icc 0 1}))
    (h₀f : ∀ y : ℝ, ‖f (I * y)‖ ≤ 1) (h₁f : ∀ y : ℝ, ‖f (1 + I * y)‖ ≤ 1)
    {y t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) :
    ‖f (t + I * y)‖ ≤ 1 := by{
      have := perturb_pointwise_norm_converge f (t+I*y)
      apply @le_of_tendsto _ _ _ _ _ (fun ε ↦ Complex.abs (perturb f ε (t + I * y))) _ _ _ _ this
      rw[eventually_nhdsWithin_iff]
      filter_upwards with ε hε
      simp at hε
      exact perturb_bound_strip hε hf h2f h₀f h₁f ht hs hts
    }


/-- Hadamard's three lines lemma/theorem on the unit strip. -/
theorem DiffContOnCl.norm_le_pow_mul_pow₀₁ {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f { z | z.re ∈ Ioo 0 1})
    (h2f : IsBounded (f '' { z | z.re ∈ Icc 0 1}))
    {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀f : ∀ y : ℝ, ‖f (I * y)‖ ≤ M₀) (h₁f : ∀ y : ℝ, ‖f (1 + I * y)‖ ≤ M₁)
    {y t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) :
    ‖f (t + I * y)‖ ≤ M₀ ^ s * M₁ ^ t := by{

      have hts'' : s = 1-t := by {
        symm
        -- Not sure why this is so messed up if I don't make it explicit
        rw[@sub_eq_of_eq_add ℝ _ (1:ℝ) t s]
        rw[add_comm]
        exact hts.symm
      }

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

      have h2g:  IsBounded (g '' { z | z.re ∈ Icc 0 1}) := by {
        obtain ⟨R, hR⟩   := (Metric.isBounded_iff_subset_ball 0).mp h2f
        simp only [subset_def, mem_image] at hR
        have hR' : ∀ x ∈ {z | z.re ∈ Icc 0 1}, Complex.abs (f x) < R := by{
          intro x hx
          specialize hR (f x) (by use x)
          simp at hR
          assumption
        }

        rw[Metric.isBounded_image_iff]
        let A := max 1 (1/M₀)
        let B := max 1 (1/M₁)
        use 2*A*B*R
        intro z hz z' hz'
        dsimp at hz
        dsimp at hz'
        simp_rw[g]
        rw[Complex.dist_eq]

        have : Complex.abs (↑M₀ ^ (z - 1) * ↑M₁ ^ (-z) * f z - ↑M₀ ^ (z' - 1) * ↑M₁ ^ (-z') * f z') ≤ Complex.abs (↑M₀ ^ (z - 1) * ↑M₁ ^ (-z) * f z) + Complex.abs (- ↑M₀ ^ (z' - 1) * ↑M₁ ^ (-z') * f z') := by{
          have := AbsoluteValue.add_le Complex.abs (↑M₀ ^ (z - 1) * ↑M₁ ^ (-z) * f z) (- ↑M₀ ^ (z' - 1) * ↑M₁ ^ (-z') * f z')
          simp at this
          simp
          exact this
          }

        simp at this
        calc
        Complex.abs (↑M₀ ^ (z - 1) * ↑M₁ ^ (-z) * f z - ↑M₀ ^ (z' - 1) * ↑M₁ ^ (-z') * f z') ≤ Complex.abs (↑M₀ ^ (z - 1)) * Complex.abs (↑M₁ ^ (-z)) * Complex.abs (f z) +
    Complex.abs (↑M₀ ^ (z' - 1)) * Complex.abs (↑M₁ ^ (-z')) * Complex.abs (f z') := this
      _ ≤ A * B * R + A * B * R := by{
        gcongr
        · exact pow_bound₀ hM₀ hz
        · exact pow_bound₁ hM₁ hz
        · apply le_of_lt; apply hR' z; exact hz
        · exact pow_bound₀ hM₀ hz'
        · exact pow_bound₁ hM₁ hz'
        · apply le_of_lt; apply hR' z'; exact hz'
      }
      _ = 2 * A * B * R := by ring
      }


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

      have hM₁': M₁^(-t)>0 := Real.rpow_pos_of_pos hM₁ (-t)
      have hM₀': M₀^(t-1)>0 := Real.rpow_pos_of_pos hM₀ (t-1)
      rw[← mul_le_mul_left hM₁',← mul_le_mul_left hM₀']
      nth_rewrite 2 [mul_comm (M₁^(-t)), ← mul_assoc]
      rw[mul_assoc, mul_assoc, ← Real.rpow_add hM₁ t (-t)]
      simp[hts'']
      rw[ ← Real.rpow_add hM₀ (t-1) (1-t)]
      simp
      rw[← mul_assoc]
      exact hgoal
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

      -- DUPLICATE FROM PREVIOUS PROOF
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
        let h : ℂ → ℂ := fun z ↦ a + (z.re *(b-a)) + I*z.im
        have hcomp: g = f ∘ h := rfl
        rw[hcomp]
        apply DiffContOnCl.comp (s:={ z | z.re ∈ Ioo a b})
        · exact hf
        · sorry --not sure what the quickest way of doing this is supposed to be
        · simp[h, MapsTo]
          intro z hz₀ hz₁
          constructor
          · apply Real.mul_pos hz₀
            simp[hab]
          · calc
            a + z.re * (b-a) < a + 1 *(b - a) := by gcongr; simp[hab]
            _ = b := by simp
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

variable (E p μ) in
def Lp.simpleLe1 := {g : SimpleFunc α E // snorm g p μ ≤ 1}

-- copied by mathlib, not in the current version

theorem NNReal.rpow_add_of_nonneg (x : ℝ≥0) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  ext; exact Real.rpow_add_of_nonneg x.2 hy hz

open ENNReal in
theorem ENNReal.rpow_add_of_nonneg {x : ℝ≥0∞} (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  induction x using recTopCoe
  · rcases hy.eq_or_lt with rfl|hy
    · rw [rpow_zero, one_mul, zero_add]
    rcases hz.eq_or_lt with rfl|hz
    · rw [rpow_zero, mul_one, add_zero]
    simp [top_rpow_of_pos, hy, hz, add_pos hy hz]
  simp [coe_rpow_of_nonneg, hy, hz, add_nonneg hy hz, NNReal.rpow_add_of_nonneg _ hy hz]

/-
lemma name (p q : ℝ≥0) (hpq : NNReal.IsConjExponent p q) (f : α →ₘ[μ] E) (hf : snorm f p μ ≠ ∞) :
snorm f p μ = sSup {∫⁻ (a : α), ‖f a‖₊ * ‖(g.1 : α → E) a‖₊ ∂ μ | g : Lp.simpleLe1 E q μ} := by
  apply le_antisymm ?_
  . apply sSup_le
    rintro b ⟨g, hg⟩
    rw [← hg]
    calc ∫⁻ a, ‖f a‖₊ * ‖(g.1 : α →ₘ[μ] E) a‖₊ ∂μ = ∫⁻ a, ((‖f ·‖₊) * (‖(g.1 : α → E) ·‖₊)) a ∂μ := lintegral_congr (by simp only [Pi.mul_apply, coe_mul, implies_true])
    _ ≤ snorm f p μ * snorm (g.1 : α →ₘ[μ] E) q μ  := by
      simp only [snorm, coe_toReal, snorm', ENNReal.coe_eq_zero,
      hpq.ne_zero, ↓reduceIte, coe_ne_top, hpq.symm.ne_zero]
      apply ENNReal.lintegral_mul_le_Lp_mul_Lq _ (NNReal.IsConjExponent.coe hpq) (AEEqFun.aemeasurable f).ennnorm (AEMeasurable.ennnorm (AEEqFun.aemeasurable _))
    _ ≤ snorm f p μ := mul_le_of_le_one_right (by positivity) g.2
  . rcases eq_or_ne (snorm f p μ) 0 with hf' | hf'
    . simp [hf']
    . set g := fun a ↦ ‖f a‖₊ ^ ((p : ℝ) - 1) * (snorm f p μ).toNNReal ^ (1 - (p : ℝ))
      have aux1 : ∫⁻ (a : α), ↑‖f a‖₊ * ↑‖g a‖₊ ∂ μ = snorm f p μ := by
        simp [g]
        calc ∫⁻ (a : α), ↑‖f a‖₊ * (↑(‖f a‖₊ ^ ((p : ℝ) - 1)) * ↑((snorm f p μ).toNNReal ^ (1 - (p : ℝ)))) ∂μ = ∫⁻ (a : α), ↑‖f a‖₊ ^ (p : ℝ) * ↑((snorm f p μ).toNNReal ^ (1 - (p : ℝ))) ∂μ := lintegral_congr (by
          intro _; rw [← mul_assoc]; congr
          rw [← ENNReal.rpow_one ↑‖f _‖₊,← ENNReal.coe_rpow_of_nonneg _ (by norm_num; exact hpq.one_le), ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num; exact hpq.one_le), ENNReal.rpow_one, add_sub_cancel]
          )
        _ = (∫⁻ (a : α), ↑‖f a‖₊ ^ (p : ℝ) ∂ μ) * ↑((snorm f p μ).toNNReal ^ (1 - (p : ℝ))) := by
          rw [lintegral_mul_const'' _ ((AEMeasurable.pow_const (AEEqFun.aemeasurable f).ennnorm) _)]
        _ = snorm f p μ := by
          have : (snorm f p μ) ^ (p : ℝ) = (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) := by
            rw [snorm_eq_lintegral_rpow_nnnorm (by norm_num; exact hpq.ne_zero) (by norm_num), ← ENNReal.rpow_mul, coe_toReal, one_div, inv_mul_cancel (by norm_num; exact hpq.ne_zero), ENNReal.rpow_one]
          rw [← this, ← ENNReal.coe_rpow_of_ne_zero (ENNReal.toNNReal_ne_zero.mpr ⟨hf', hf⟩), ENNReal.coe_toNNReal hf, ← ENNReal.rpow_add _ _ hf' hf, add_sub_cancel, ENNReal.rpow_one]
      sorry
-/

open Filter Topology in
example (f : ℕ → ℝ≥0∞) (a : ℝ≥0∞) (S : Set ℝ≥0∞) (h : ∀ n, f n ∈ S) (hf : Tendsto f atTop (𝓝 a)) : a ≤ sSup S := by
  rw [← Tendsto.limsup_eq hf]
  apply le_trans limsup_le_iSup
  rw [iSup_le_iff]
  intro i
  apply le_sSup (h i)

variable (f : α → ℂ) (a : ℝ) (t : α)

def sgn (z : ℂ) : ℂ := if z = 0 then 0 else z / ‖z‖

-- copied
theorem _root_.Real.nnnorm_rpow_of_nonneg {x y : ℝ} (hx : 0 ≤ x) : ‖x ^ y‖₊ = ‖x‖₊ ^ y := by
  ext; exact Real.norm_rpow_of_nonneg hx

#check lintegral
#check α →ₘ[μ] ℂ

example (p q : ℝ≥0) (hpq : NNReal.IsConjExponent p q) (f : α → ℂ) (hf : AEMeasurable f μ) (hf' : snorm f p μ ≠ ∞) :
snorm f p μ ≤ sSup {snorm (f * (g.1 : α → ℂ)) 1 μ | g : Lp.simpleLe1 ℂ q μ} := by
  sorry

def toLpSimpLe1 (q : ℝ≥0) (hq : q ≠ 0) (f : SimpleFunc α ℝ≥0) (h : (∫⁻ a, (f a) ^ (q : ℝ) ∂ μ) ^ (q : ℝ)⁻¹ ≤ 1) : Lp.simpleLe1 ℂ q μ where
  val := {
    toFun := fun x ↦ ((f x) : ℂ)
    measurableSet_fiber' := by
      intro x
      rcases eq_or_ne x.im 0 with (H' | H')
      rcases le_or_lt 0 x.re with (H | H)
      convert f.measurableSet_fiber' x.re.toNNReal
      ext y
      simp
      constructor
      intro h
      ext
      rw [← h, Complex.ofReal_re, Real.coe_toNNReal _ (by norm_num)]
      intro h
      rw [h, Real.coe_toNNReal _ H]
      apply Complex.ext
      rw [Complex.ofReal_re]
      rw [Complex.ofReal_im, H']
      convert MeasurableSet.empty
      ext y
      simp
      contrapose! H
      rw [← H]
      apply NNReal.coe_nonneg _
      convert MeasurableSet.empty
      ext y
      simp
      contrapose! H'
      rw [← H', Complex.ofReal_im]
    finite_range' := by
      have : (range fun x ↦ (((f x) : ℝ) : ℂ)) = ofReal' '' (range fun x ↦ f x) := by apply Set.range_comp ofReal'
      rw [this]
      apply Set.Finite.image _
      have : (range fun x ↦ ((f x) : ℝ)) = toReal '' (range fun x ↦ f x) := by apply Set.range_comp toReal
      rw [this]
      apply Set.Finite.image _ f.finite_range'
  }
  property := by
    simp [snorm, snorm', hq]
    exact h

section
open SimpleFunc

example (p q : ℝ≥0) (hpq : NNReal.IsConjExponent p q) (f : α → ℂ) :
sSup {∫⁻ (a : α), ‖f a‖₊ * ‖g.1 a‖₊ ∂ μ | g : {f : SimpleFunc α ℝ≥0 // (∫⁻ a, (f a) ^ (q : ℝ) ∂ μ) ^ (q : ℝ)⁻¹ ≤ 1} } ≤ sSup {snorm (f * (g.1 : α → ℂ)) 1 μ | g : Lp.simpleLe1 ℂ q μ} := by
  apply sSup_le_sSup
  rintro x ⟨g, hg⟩
  set g' : Lp.simpleLe1 ℂ q μ := toLpSimpLe1 q hpq.symm.ne_zero _ g.2
  use g'
  convert hg
  simp [snorm, snorm', g', toLpSimpLe1]

example (p q : ℝ≥0) (hpq : NNReal.IsConjExponent p q) (f : α → ℂ) (hf : Measurable f) (hf' : snorm f p μ ≠ ∞) :
snorm f p μ ≤ sSup {∫⁻ (a : α), ‖f a‖₊ * (g.1 a) ∂ μ | g : {f : SimpleFunc α ℝ≥0∞ // (∫⁻ a, (f a) ^ (q : ℝ) ∂ μ) ^ (q : ℝ)⁻¹ ≤ 1} } := by
  rcases eq_or_ne (snorm f p μ) 0 with hf0 | hf0
  . simp [hf0]
  . set g : α → ℝ≥0∞ := fun a ↦ (‖f a‖ ^ ((p : ℝ) - 1) * (snorm f p μ).toReal ^ (1 - (p : ℝ))).toNNReal
    set g' := SimpleFunc.eapprox g
    have aux (n : ℕ) : (∫⁻ a, (g' n a) ^ (q : ℝ) ∂ μ) ^ (q : ℝ)⁻¹ ≤ 1 := sorry
    have cru : snorm f p μ = ∫⁻ (a : α), ↑‖f a‖₊ * (g a) ∂ μ := sorry
    -- want to prove `∫ f g = ⊔ ∫ f gᵢ ≤ sSup ∫ f g`
    -- need to show `∫ epprox ≤ 1`

def aux_func (μ : Measure α) (p : ℝ≥0) (f : α → ℂ) : α → ℝ≥0∞ := fun a ↦ (‖f a‖ ^ ((p : ℝ) - 1) * (snorm f p μ).toReal ^ (1 - (p : ℝ))).toNNReal

-- show `∫ epprox ≤ 1` -- pretty funny that I have to use a more stronger lemma `iSup_eapprox_apply`
-- one problem here, seems to need `Measurable`. `AEMeasurable` not enough??
lemma lemma3 (p : ℝ≥0) (f : α → ℝ≥0∞) (hf : Measurable f) (h : (∫⁻ a, (f a) ^ (p : ℝ) ∂ μ) ^ (p : ℝ)⁻¹ ≤ 1 ) (n : ℕ) :
  (∫⁻ a, (eapprox f n a) ^ (p : ℝ) ∂ μ) ^ (p : ℝ)⁻¹ ≤ 1 := by
  apply le_trans ?_ h
  gcongr
  rw [← iSup_eapprox_apply f hf]
  apply le_iSup _ n

-- show `⊔ ∫ f gᵢ ≤ sSup ∫ f g`
example (p q : ℝ≥0) (hpq : NNReal.IsConjExponent p q) (f : α → ℂ) (hf : Measurable f) (hf' : snorm f p μ ≠ ∞) : ⨆ n, ∫⁻ (a : α), ‖f a‖₊ * (eapprox (aux_func μ p f) n a) ∂ μ ≤ sSup {∫⁻ (a : α), ‖f a‖₊ * (g.1 a) ∂ μ | g : {f : SimpleFunc α ℝ≥0∞ // (∫⁻ a, (f a) ^ (q : ℝ) ∂ μ) ^ (q : ℝ)⁻¹ ≤ 1} } := by
  apply iSup_le
  intro n
  apply le_sSup
  simp
  use eapprox (aux_func μ p f) n
  constructor
  . apply lemma3 _ _
    apply Measurable.comp (by measurability)
    have : (fun x ↦ (‖f x‖ ^ ((p : ℝ) - 1) * (snorm f p μ).toReal ^ (1 - (p : ℝ))).toNNReal) = Real.toNNReal ∘ fun x ↦ ‖f x‖ ^ ((p : ℝ) - 1) * (snorm f p μ).toReal ^ (1 - (p : ℝ)) := rfl
    rw [this]
    -- this is weird!!!
    apply @Measurable.comp _ _ _ _  Real.measurableSpace _
    measurability
    apply Measurable.mul_const _ ((snorm f p μ).toReal ^ (1 - (p : ℝ)))
    apply Measurable.pow_const
    apply Measurable.norm hf
    sorry
  . rfl

-- want to prove `∫ f g = ⊔ ∫ f gᵢ`
example {f g: α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ a, (f * g) a ∂μ = ⨆ n, ∫⁻ a, (f * (eapprox g n)) a ∂μ := by
    calc  ∫⁻ a, (f * g) a ∂μ = ∫⁻ a, ⨆ n, (f * (eapprox g n)) a ∂μ := by {
       congr
       ext a
       simp only [Pi.mul_apply, ← ENNReal.mul_iSup, iSup_eapprox_apply g hg]
       }
    _ = ⨆ n, ∫⁻ a, (f * (eapprox g n)) a ∂μ := by
      apply lintegral_iSup
      . measurability
      . intro i j h
        intro a
        simp only [Pi.mul_apply]
        gcongr
        exact monotone_eapprox g h a
end


#exit
lemma name (p q : ℝ≥0) (hpq : NNReal.IsConjExponent p q) (f : α → ℂ) (hf : AEMeasurable f μ) (hf' : snorm f p μ ≠ ∞) :
snorm f p μ = sSup {snorm (f * (g.1 : α → ℂ)) 1 μ | g : Lp.simpleLe1 ℂ q μ} := by
  apply le_antisymm ?_
  . apply sSup_le
    rintro b ⟨g, hg⟩
    rw [← hg]
    calc snorm (f * (g.1 : α → ℂ)) 1 μ = ∫⁻ a, ‖f a‖₊ * ‖(g.1 : α → ℂ) a‖₊ ∂μ := by simp [snorm, snorm']
    _ = ∫⁻ a, ((‖f ·‖₊) * (‖(g.1 : α → ℂ) ·‖₊)) a ∂μ := lintegral_congr (by simp only [Pi.mul_apply, coe_mul, implies_true])
    _ ≤ snorm f p μ * snorm (g.1 : α →ₘ[μ] ℂ) q μ  := by
      simp only [snorm, coe_toReal, snorm', ENNReal.coe_eq_zero,
      hpq.ne_zero, ↓reduceIte, coe_ne_top, hpq.symm.ne_zero]
      apply ENNReal.lintegral_mul_le_Lp_mul_Lq _ (NNReal.IsConjExponent.coe hpq) hf.ennnorm (AEMeasurable.ennnorm (AEEqFun.aemeasurable _))
    _ ≤ snorm f p μ := mul_le_of_le_one_right (by positivity) g.2
  . rcases eq_or_ne (snorm f p μ) 0 with hf0 | hf0
    . simp [hf0]
    . set g : α → ℂ := fun a ↦ (‖f a‖ ^ ((p : ℝ) - 1) : ℝ) * ((snorm f p μ).toReal ^ (1 - (p : ℝ)) : ℝ)
      have (a : α) : ‖g a‖₊ = (↑(‖f a‖₊ ^ ((p : ℝ) - 1)) * ↑((snorm f p μ).toNNReal ^ (1 - (p : ℝ)))) := by
        simp only [nnnorm_mul, nnnorm_real, g]
        congr
        rw [Real.nnnorm_rpow_of_nonneg (norm_nonneg _)]
        congr 1
        ext
        simp only [coe_nnnorm, norm_norm]
        rw [Real.nnnorm_rpow_of_nonneg]
        congr 1
        ext
        simp only [coe_nnnorm]
        rw [Real.norm_of_nonneg]
        norm_cast
        repeat' apply ENNReal.toReal_nonneg

      have aux0 : (snorm f p μ) ^ (p : ℝ) = (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) := by
            rw [snorm_eq_lintegral_rpow_nnnorm (by norm_num; exact hpq.ne_zero) (by norm_num), ← ENNReal.rpow_mul, coe_toReal, one_div, inv_mul_cancel (by norm_num; exact hpq.ne_zero), ENNReal.rpow_one]


      have aux1 : ∫⁻ (a : α), ↑‖f a‖₊ * ↑‖g a‖₊ ∂ μ = snorm f p μ := by
        simp only [this, nnnorm_mul, nnnorm_real, coe_mul]
        calc ∫⁻ (a : α), ↑‖f a‖₊ * (↑(‖f a‖₊ ^ ((p : ℝ) - 1)) * ↑((snorm f p μ).toNNReal ^ (1 - (p : ℝ)))) ∂μ = ∫⁻ (a : α), ↑‖f a‖₊ ^ (p : ℝ) * ↑((snorm f p μ).toNNReal ^ (1 - (p : ℝ))) ∂μ := lintegral_congr (by
          intro _; rw [← mul_assoc]; congr
          rw [← ENNReal.rpow_one ↑‖f _‖₊,← ENNReal.coe_rpow_of_nonneg _ (by norm_num; exact hpq.one_le), ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num; exact hpq.one_le), ENNReal.rpow_one, add_sub_cancel]
          )
        _ = (∫⁻ (a : α), ↑‖f a‖₊ ^ (p : ℝ) ∂ μ) * ↑((snorm f p μ).toNNReal ^ (1 - (p : ℝ))) := by
          rw [lintegral_mul_const'' _ ((AEMeasurable.pow_const hf.ennnorm) _)]
        _ = snorm f p μ := by
          rw [← aux0, ← ENNReal.coe_rpow_of_ne_zero (ENNReal.toNNReal_ne_zero.mpr ⟨hf0, hf'⟩), ENNReal.coe_toNNReal hf', ← ENNReal.rpow_add _ _ hf0 hf', add_sub_cancel, ENNReal.rpow_one]

      have aux2 : snorm g q μ = 1 := by
        simp [snorm, snorm', hpq.symm.ne_zero]; simp only [this]
        calc (∫⁻ (a : α), ↑(‖f a‖₊ ^ ((p : ℝ) - 1) * (snorm f p μ).toNNReal ^ (1 - (p : ℝ))) ^ (q : ℝ) ∂μ) ^ (q : ℝ)⁻¹ = (∫⁻ (a : α), (↑‖f a‖₊ ^ (((p : ℝ) - 1) * q) * (snorm f p μ).toNNReal ^ ((1 - (p : ℝ)) * q)) ∂μ) ^ (q : ℝ)⁻¹ := by congr 1; apply lintegral_congr (by intro a; simp; rw [ENNReal.mul_rpow_of_nonneg (hz := by norm_num), ← ENNReal.coe_rpow_of_nonneg _ (by norm_num; exact hpq.one_le), ← ENNReal.coe_rpow_of_ne_zero (by rw [ENNReal.toNNReal_ne_zero]; exact ⟨hf0, hf'⟩), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul])
        _ = 1 := by
          rw [lintegral_mul_const'' _ ((AEMeasurable.pow_const hf.ennnorm) _)]
          rw [(isConjExponent_coe.mpr hpq).sub_one_mul_conj]
          rw [ENNReal.coe_toNNReal hf', ← aux0]
          rw [← ENNReal.rpow_add _ _ hf0 hf']
          rw [sub_mul (1 : ℝ), (isConjExponent_coe.mpr hpq).mul_eq_add]
          rw [one_mul, sub_add_cancel_right, add_right_neg, ENNReal.rpow_zero,
            ENNReal.one_rpow]




      sorry








#exit
-- prove a variant of Hölder's inequality

lemma ENNReal.rpow_add_of_pos {x : ENNReal} (y : ℝ) (z : ℝ) (hy : 0 < y) (hz : 0 < z) :
x ^ (y + z) = x ^ y * x ^ z := by
  cases x with
  | top => simp [hy, hz, add_pos hy hz]
  | coe x =>
      rcases eq_or_ne ↑x 0 with hx0 | hx0'
      simp only [hx0, coe_zero, add_pos hy hz, zero_rpow_of_pos, hy, hz, mul_zero]
      apply ENNReal.rpow_add <;> simp [hx0']

lemma ENNReal.essSup_const_rpow (f : α → ℝ≥0∞) {r : ℝ} (hr : 0 < r) : (essSup f μ) ^ r = essSup (fun x ↦ (f x) ^ r) μ :=
  OrderIso.essSup_apply (g := ENNReal.orderIsoRpow r hr) _ _

def InSegment.toIsConjugateExponent (p₀ p₁ p : ℝ≥0∞) (t s : ℝ≥0)  (hp₀ : 0 < p₀)
(hp₁ : 0 < p₁) (hp₀₁ : p₀ < p₁) (hp : s * p₀⁻¹ + t * p₁⁻¹ = p⁻¹)
(hp0' : p ≠ 0) (ht0' : t ≠ 0) (hs0' : s ≠ 0) (hpt' : p ≠ ⊤) (hp₁t : p₁ ≠ ⊤) :
Real.IsConjExponent (p₀⁻¹ * (s : ℝ≥0∞) * p).toReal ⁻¹ (p₁⁻¹ * (t : ℝ≥0∞) * p).toReal ⁻¹ where
  one_lt := by
    --- [one_lt_inv (a := (p₀⁻¹ * ↑s * p).toReal)] does not work ha??
    rw [lt_inv zero_lt_one (ENNReal.toReal_pos (mul_ne_zero (mul_ne_zero (ENNReal.inv_ne_zero.mpr (LT.lt.ne_top hp₀₁)) (by rwa [ENNReal.coe_ne_zero])) hp0') (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hp₀.ne.symm) ENNReal.coe_ne_top) hpt')), mul_comm p₀⁻¹]
    apply_fun (fun x ↦ x * p) at hp
    rw [add_mul, ENNReal.inv_mul_cancel hp0' hpt'] at hp
    calc (↑s * p₀⁻¹ * p).toReal < (↑s * p₀⁻¹ * p + ↑t * p₁⁻¹ * p).toReal := ENNReal.toReal_strict_mono (hp ▸ one_ne_top) <| ENNReal.lt_add_right ((ENNReal.add_ne_top (b := ↑t * p₁⁻¹ * p)).mp (hp ▸ one_ne_top)).1 (mul_ne_zero (mul_ne_zero (by rwa [ENNReal.coe_ne_zero]) (by rwa [ENNReal.inv_ne_zero])) hp0')
    _ = 1⁻¹ := by simp [hp]
  inv_add_inv_conj := by
    rw [inv_inv, inv_inv, ← ENNReal.toReal_add (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hp₀.ne.symm) ENNReal.coe_ne_top) hpt') (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hp₁.ne.symm) ENNReal.coe_ne_top) hpt'), ← ENNReal.one_toReal]
    congr
    apply_fun (fun x ↦ x * p) at hp
    rwa [add_mul, ENNReal.inv_mul_cancel hp0' hpt', mul_comm (ofNNReal s), mul_comm (ofNNReal t)] at hp


-- can remove hpt'
lemma lintegral_mul_le_segment_exponent_aux (p₀ p₁ p : ℝ≥0∞) (t s : ℝ≥0) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀₁ : p₀ < p₁)
(hp : s * p₀⁻¹ + t * p₁⁻¹ = p⁻¹) (f : α →ₘ[μ] E) (hp0' : p ≠ 0) (ht0' : t ≠ 0)
(hs0' : s ≠ 0) :
∫⁻ (a : α), ↑‖f a‖₊ ^ (↑s * p.toReal) * ↑‖f a‖₊ ^ (↑t * p.toReal) ∂μ ≤
  snorm (↑f) p₀ μ ^ (↑s * p.toReal) * snorm (↑f) p₁ μ ^ (↑t * p.toReal) := by
  rcases eq_or_ne p ⊤ with hpt | hpt'
  simp [hpt, add_eq_zero, hs0', ht0'] at hp
  exact False.elim <| ne_top_of_lt hp₀₁ hp.1

  rcases eq_or_ne p₁ ⊤ with hp₁t | hp₁t'
  simp only [snorm, (ne_of_lt hp₀).symm, ↓reduceIte, LT.lt.ne_top hp₀₁, snorm',
  one_div, hp₁t, top_ne_zero, snormEssSup]
  simp only [hp₁t, inv_top, mul_zero, add_zero] at hp
  apply_fun (fun x ↦ x * p₀) at hp
  rw [mul_assoc, ENNReal.inv_mul_cancel (ne_of_lt hp₀).symm (LT.lt.ne_top hp₀₁), mul_one] at hp
  have hp_aux : s * p = p₀ := by rw [hp, mul_assoc, mul_comm p₀, ← mul_assoc,
  ENNReal.inv_mul_cancel hp0' hpt', one_mul]

  apply le_trans (lintegral_mul_le_one_top _ (AEMeasurable.pow_const f.measurable.ennnorm.aemeasurable _)) (le_of_eq _)
  congr
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_one (∫⁻ (a : α), ↑‖f a‖₊ ^ (↑s * p.toReal) ∂μ)]
  congr; ext; congr
  simp only [← hp_aux, toReal_mul, coe_toReal] -- lemma? to rw
  simp only [← hp_aux, toReal_mul, coe_toReal, mul_inv_rev, mul_assoc p.toReal⁻¹, ← mul_assoc, inv_mul_cancel (by rwa [NNReal.coe_ne_zero]), one_mul,
    inv_mul_cancel (ENNReal.toReal_ne_zero.mpr ⟨hp0', hpt'⟩)]

  apply (ENNReal.essSup_const_rpow _ ?_).symm
  exact Real.mul_pos (lt_of_le_of_ne (NNReal.coe_nonneg t) (NNReal.coe_ne_zero.mpr ht0').symm) (ENNReal.toReal_pos hp0' hpt')

  simp only [snorm, (ne_of_lt hp₀).symm, ↓reduceIte, LT.lt.ne_top hp₀₁, snorm',
  one_div, (ne_of_lt hp₁).symm, hp₁t', ge_iff_le]
  apply le_trans (ENNReal.lintegral_mul_le_Lp_mul_Lq μ (by apply InSegment.toIsConjugateExponent p₀ p₁ p t s; repeat assumption) (AEMeasurable.pow_const f.measurable.ennnorm.aemeasurable _) (AEMeasurable.pow_const f.measurable.ennnorm.aemeasurable _)) (le_of_eq _)

  simp only [← ENNReal.rpow_mul]
  congr

  simp only [toReal_mul, coe_toReal, mul_inv_rev]
  congr
  rw [toReal_inv, inv_inv, ← mul_assoc, ← mul_assoc, mul_comm _ p.toReal, mul_assoc p.toReal, mul_comm s.toReal, ← mul_assoc, mul_assoc _ s.toReal,
  mul_inv_cancel (ENNReal.toReal_ne_zero.mpr ⟨hp0', hpt'⟩), mul_inv_cancel (by rwa [NNReal.coe_ne_zero]), one_mul, one_mul]

  rotate_left 1

  simp only [toReal_mul, coe_toReal, mul_inv_rev]
  congr
  rw [toReal_inv, inv_inv, ← mul_assoc, ← mul_assoc, mul_comm _ p.toReal, mul_assoc p.toReal, mul_comm t.toReal, ← mul_assoc, mul_assoc _ t.toReal,
  mul_inv_cancel (ENNReal.toReal_ne_zero.mpr ⟨hp0', hpt'⟩), mul_inv_cancel (by rwa [NNReal.coe_ne_zero]), one_mul, one_mul]

  repeat' simp [← mul_assoc, ENNReal.toReal_inv]

lemma lintegral_mul_le_segment_exponent (p₀ p₁ p : ℝ≥0∞) (t s : ℝ≥0) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀₁ : p₀ < p₁)
(hp : s * p₀⁻¹ + t * p₁⁻¹ = p⁻¹) (hst : s + t = 1)
(f : α →ₘ[μ] E) (h₀f : snorm f p₀ μ ≠ ⊤) (h₁f : snorm f p₁ μ ≠ ⊤)
 : snorm f p μ ≤ (snorm f p₀ μ) ^ s.toReal * (snorm f p₁ μ) ^ t.toReal := by

  have hp0' : p ≠ 0 := by by_contra h; simp only [h, ENNReal.inv_zero, add_eq_top,
  mul_eq_top, ne_eq, ENNReal.coe_eq_zero, inv_eq_top, (ne_of_lt hp₀).symm, and_false,
  coe_ne_top, ENNReal.inv_eq_zero, false_and, or_self, (ne_of_lt hp₁).symm] at hp

  rcases eq_or_ne t 0 with ht0 | ht0'
  simp only [ht0, add_zero] at hst
  simp only [hst, ENNReal.coe_one, one_mul, ht0, ENNReal.coe_zero, zero_mul, add_zero, inv_inj] at hp
  simp only [hp, hst, NNReal.coe_one, ENNReal.rpow_one, ht0, NNReal.coe_zero, ENNReal.rpow_zero, mul_one, le_refl]

  rcases eq_or_ne s 0 with hs0 | hs0'
  simp only [hs0, zero_add] at hst
  simp only [hs0, ENNReal.coe_zero, zero_mul, hst, ENNReal.coe_one, one_mul, zero_add,
  inv_inj] at hp
  simp only [hp, hs0, NNReal.coe_zero, ENNReal.rpow_zero, hst, NNReal.coe_one, ENNReal.rpow_one, one_mul, le_refl]

  rcases eq_or_ne p ⊤ with hpt | hpt'
  . simp [hpt, add_eq_zero, hs0', ht0'] at hp
    exact False.elim <| ne_top_of_lt hp₀₁ hp.1

  . calc snorm f p μ = (∫⁻ (a : α), ↑‖f a‖₊ ^ p.toReal ∂μ) ^ p.toReal⁻¹ := by simp [snorm, hp0', hpt', snorm']
    _ = (∫⁻ (a : α), ↑‖f a‖₊ ^ (s * p.toReal) *  ↑‖f a‖₊ ^ (t * p.toReal) ∂μ) ^ p.toReal⁻¹ := by
      congr; ext
      rw [← ENNReal.rpow_add_of_pos (s * p.toReal) (t * p.toReal) ?_ ?_, ← add_mul, ← NNReal.coe_add, hst, NNReal.coe_one, one_mul]
      <;> apply Real.mul_pos (lt_of_le_of_ne (NNReal.coe_nonneg _) (NNReal.coe_ne_zero.mpr (by assumption)).symm) (ENNReal.toReal_pos hp0' hpt')
    _ ≤ ((snorm f p₀ μ) ^ (s * p.toReal) *  (snorm f p₁ μ) ^ (t * p.toReal)) ^ p.toReal⁻¹ := by
      gcongr
      apply lintegral_mul_le_segment_exponent_aux
      <;> assumption -- apply should do this automatically, what's wrong?
    _ = (snorm f p₀ μ) ^ s.toReal * (snorm f p₁ μ) ^ t.toReal := by
      rw [ENNReal.mul_rpow_of_ne_top, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      repeat rw [mul_assoc, mul_inv_cancel (ENNReal.toReal_ne_zero.mpr ⟨hp0', hpt'⟩), mul_one]
      repeat' apply ENNReal.rpow_ne_top_of_nonneg (mul_nonneg (NNReal.coe_nonneg _) ENNReal.toReal_nonneg) (by assumption)


/-- An operator has strong type (p, q) if it is bounded as an operator on `L^p → L^q`.
`HasStrongType T p p' μ ν c` means that `T` has strong type (p, q) w.r.t. measures `μ`, `ν`
and constant `c`.  -/
def HasStrongType {E E' α α' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → E) → (α' → E'))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0) : Prop :=
  ∀ f : α → E, Memℒp f p μ → AEStronglyMeasurable (T f) ν ∧ snorm (T f) p' ν ≤ c * snorm f p μ

-- variable (E p q μ) in
-- /-- The additive subgroup of `α →ₘ[μ] E` consisting of the simple functions in both
-- `L^p` and `L^q`. This is denoted `U` in [Ian Tice]. -/
-- def Lp.simpleFunc2 : AddSubgroup (α →ₘ[μ] E) :=
--   (Lp.simpleFunc E p μ).map (AddSubgroup.subtype _) ⊓
--   (Lp.simpleFunc E q μ).map (AddSubgroup.subtype _)

/- to do: `f ∈ Lp.simpleFunc2 E p q μ` iff
`snorm f p μ < ∞ ∧ snorm f q μ < ∞ ∧ f is a simple function`. -/

-- /-- A normed operator `T` is bounded on `Lp.simpleFunc2 p₀ p₁ q` w.r.t. the `L^p₀`
-- where the codomain uses the `L^q` norm. -/
-- def SBoundedBy (T : (α →ₘ[μ] E₁) → β →ₘ[ν] E₂) (p₀ p₁ q : ℝ≥0∞) (C : ℝ) : Prop :=
--   ∀ (f : α →ₘ[μ] E₁), f ∈ Lp.simpleFunc2 E₁ p₀ p₁ μ →
--   snorm (T f) q ν ≤ ENNReal.ofReal C * snorm f p₀ μ

/-- Riesz-Thorin interpolation theorem -/
theorem exists_lnorm_le_of_subadditive_of_lbounded {p₀ p₁ q₀ q₁ : ℝ≥0∞} {M₀ M₁ : ℝ≥0}
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hν : q₀ = ∞ → q₁ = ∞ → SigmaFinite ν)
    (T : (α → E₁) →ₗ[ℂ] β → E₂)
    (h₀T : HasStrongType T p₀ q₀ μ ν M₀)
    (h₁T : HasStrongType T p₁ q₁ μ ν M₁)
    {θ η : ℝ≥0} (hθη : θ + η = 1)
    {p q : ℝ≥0∞} (hp : p⁻¹ = (1 - θ) / p₀ + θ / p₁) (hr : q⁻¹ = (1 - θ) / q₀ + θ / q₁) :
    HasStrongType T p q μ ν (M₀ ^ (η : ℝ) * M₁ ^ (θ : ℝ)) := by sorry
