import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Order.Filter.Basic
import BonnAnalysis.Dual
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import BonnAnalysis.StrongType

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

lemma Real.le_one_of_add_nonneg_eq_one {t s : ℝ} (hs : 0 ≤ s) (hts : t + s = 1) : t ≤ 1 := by{
  calc
  t = 1 - s := eq_sub_of_add_eq hts
  _ ≤ 1 := by simp[hs]
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

lemma abs_fun_nonempty (f: ℂ → ℂ) : ((fun z ↦ Complex.abs (f z))'' { z | z.re ∈ Icc 0 1}).Nonempty := by{
  simp
  use 0
  simp
}

lemma abs_fun_bounded {f:ℂ → ℂ} (h2f : IsBounded (f '' { z | z.re ∈ Icc 0 1})) : BddAbove ((fun z ↦ Complex.abs (f z))'' { z | z.re ∈ Icc 0 1}) := by{
  simp[BddAbove, upperBounds]
  obtain ⟨R, hR⟩:= (isBounded_iff_forall_norm_le).mp h2f
  use R
  simp
  intro r z hz₁ hz₂ habs
  rw[← habs]
  exact hR (f z) (by use z; simp[hz₁, hz₂])
}

/- Some technical lemmas to apply the maximum modulus principle -/
lemma strip_prod : { z:ℂ  | z.re ∈ Ioo 0 1} = (Ioo 0 1 : Set ℝ) ×ℂ univ := by{
  ext z
  simp[Complex.mem_reProdIm]
}

lemma clstrip_prod : {z: ℂ | z.re ∈ Icc 0 1} = (Icc 0 1 : Set ℝ) ×ℂ univ := by{
  ext z
  simp[Complex.mem_reProdIm]
}


lemma isPreconnected_strip : IsPreconnected { z : ℂ | z.re ∈ Ioo 0 1} := by{
  have : { z : ℂ | z.re ∈ Ioo 0 1} = ⇑equivRealProdCLM.toHomeomorph ⁻¹' ((Ioo 0 1 : Set ℝ) ×ˢ  (univ: Set ℝ)) := by{
    ext z
    simp
  }
  rw[this, Homeomorph.isPreconnected_preimage Complex.equivRealProdCLM.toHomeomorph]
  exact IsPreconnected.prod isPreconnected_Ioo isPreconnected_univ
}

lemma isOpen_strip : IsOpen { z : ℂ | z.re ∈ Ioo 0 1} := by{
  rw[strip_prod]
  exact IsOpen.reProdIm isOpen_Ioo isOpen_univ
}

lemma isClosed_clstrip : IsClosed { z : ℂ | z.re ∈ Icc 0 1} := by{
  rw[clstrip_prod]
  exact IsClosed.reProdIm isClosed_Icc isClosed_univ
}


lemma closure_strip : closure { z:ℂ  | z.re ∈ Ioo 0 1} = { z: ℂ  | z.re ∈ Icc 0 1} := by{
  rw[strip_prod, clstrip_prod]
  rw [Complex.closure_reProdIm, closure_univ, closure_Ioo]
  norm_num
}


/-- Hadamard's three lines lemma/theorem on the unit strip with bounds M₀=M₁=1 and vanishing at infinity condition. -/
theorem DiffContOnCl.norm_le_pow_mul_pow''' {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f { z | z.re ∈ Ioo 0 1})
    (h2f : IsBounded (f '' { z | z.re ∈ Icc 0 1}))
    (h₀f : ∀ y : ℝ, ‖f (I * y)‖ ≤ 1) (h₁f : ∀ y : ℝ, ‖f (1 + I * y)‖ ≤ 1)
    {y t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) (hlim: Tendsto f (Bornology.cobounded ℂ ⊓ Filter.principal ({ z: ℂ | z.re ∈ Icc 0 1})) (nhds 0)) :
    ‖f (t + I * y)‖ ≤ 1 := by{

      by_cases h : ∃ w : ℂ, w ∈ {z | z.re ∈ Icc 0 1} ∧ Complex.abs (f w) > 0
      · obtain ⟨u, hu1, hu2, hu3⟩ :=  exists_seq_tendsto_sSup (abs_fun_nonempty f) (abs_fun_bounded h2f)
        simp at hu3
        obtain ⟨z, hz⟩ := Classical.axiom_of_choice hu3
        have hzu : (norm ∘ f) ∘ z = u := by{
          funext n
          specialize hz n
          rw[← hz.2]
          rfl
        }

        have hrange₁ : range z ⊆ {w | (0 ≤ w.re ∧ w.re ≤ 1)} := by{
          simp[range]
          intro n
          specialize hz n
          exact hz.1
        }

        have hrangeclos : closure (range z) ⊆ {w | (0 ≤ w.re ∧ w.re ≤ 1)} := by{
          apply (IsClosed.closure_subset_iff isClosed_clstrip).mpr
          simp
          exact hrange₁
        }


        have hbz : IsBounded (range z) := by{
          have : Disjoint (Bornology.cobounded ℂ ⊓ Filter.principal ({ z: ℂ | z.re ∈ Icc 0 1})) (Filter.map z atTop) := by{
            apply Tendsto.disjoint (f:= norm ∘ f) (lb₁ := nhds 0) (lb₂ := (nhds (sSup ((fun z ↦ Complex.abs (f z)) '' {z | z.re ∈ Icc 0 1}))))
            · have : norm ∘ f = (fun z ↦ Complex.abs (f z) ) := by rfl
              rw[this]
              nth_rewrite 2 [← @norm_zero ℂ _]
              apply Filter.Tendsto.norm
              exact hlim
            · simp
              apply ne_of_lt
              obtain ⟨w, hw1, hw2⟩ := h
              calc
              0 < Complex.abs (f w) := hw2
              _ ≤ sSup ((fun z ↦ Complex.abs (f z)) '' {z | 0 ≤ z.re ∧ z.re ≤ 1}) := le_csSup (abs_fun_bounded h2f) (by simp; use w; simp at hw1; simp[hw1])
            · simp
              rw[hzu]
              simp at hu2
              exact hu2
          }
          rw[Filter.disjoint_iff] at this
          obtain ⟨A,hA, B, hB, hAB⟩ := this
          rw[Filter.mem_map] at hB
          simp at hB
          obtain ⟨N, hN⟩ := hB

          have hB' : IsBounded (B ∩ {w : ℂ | w.re ∈ Icc 0 1}) := by{
            obtain ⟨A₁, hA₁, A₂, hA₂, hAint⟩ := Filter.mem_inf_iff.mp hA
            rw[hAint] at hAB
            have : A₁ ∩ A₂ = (A₁ᶜ ∪ A₂ᶜ)ᶜ := by simp
            rw[this, Set.disjoint_compl_left_iff_subset] at hAB
            have hint' : A₂ᶜ ∩ {w | w.re ∈ Icc 0 1} = ∅ := by{
              rw[mem_principal] at hA₂
              rw[← Set.diff_eq_compl_inter, Set.diff_eq_empty]
              exact hA₂
            }

            have : B ∩ {w | w.re ∈ Icc 0 1} ⊆ A₁ᶜ := by{
              calc
              B ∩ {w | w.re ∈ Icc 0 1} ⊆ (A₁ᶜ ∪ A₂ᶜ) ∩ {w | w.re ∈ Icc 0 1} := inter_subset_inter hAB (by simp)
              _ = (A₁ᶜ ∩ {w | w.re ∈ Icc 0 1}) ∪ (A₂ᶜ ∩ {w | w.re ∈ Icc 0 1}) := union_inter_distrib_right A₁ᶜ A₂ᶜ {w | w.re ∈ Icc 0 1}
              _ = A₁ᶜ ∩ {w | w.re ∈ Icc 0 1} := by rw[hint']; simp
              _ ⊆ A₁ᶜ := inter_subset_left
            }

            apply Bornology.IsBounded.subset ?_ this
            exact IsCobounded.compl hA₁
          }

          rw[isBounded_iff_forall_norm_le] at hB'
          obtain ⟨M, hM⟩ := hB'

          have hbd : IsBounded (range (fun (i: Fin N) ↦ ‖ z i‖ )) := by{
            apply Set.Finite.isBounded
            apply Set.finite_range
          }

          obtain ⟨M', hM'⟩ := isBounded_iff_forall_norm_le.mp hbd
          simp at hM'
          rw[isBounded_iff_forall_norm_le]
          use max M M'
          intro x hx
          simp at hx
          obtain ⟨n, hn⟩ := hx
          rw[← hn]
          by_cases hc: N ≤ n
          · specialize hN n hc
            specialize hM (z n) (by simp[hN]; specialize hz n; simp[hz])
            calc
            _ ≤ _ := hM
            _ ≤ _ := le_max_left M M'
          · simp at hc
            specialize hM' (Fin.mk n hc)
            simp at hM'
            calc
            _ ≤ _ := hM'
            _ ≤ _ := le_max_right M M'
        }

        obtain ⟨z',hz', φ, hφ₁, hφ₂⟩ := tendsto_subseq_of_bounded (x:=z) hbz (by simp)

        have hu': Tendsto u atTop (nhds (Complex.abs (f z'))) := by {
          rw[tendsto_iff_tendsto_subseq_of_monotone hu1 (StrictMono.tendsto_atTop hφ₁)]
          rw[← hzu]
          apply Tendsto.comp (y:= nhdsWithin z' {w:ℂ | w.re ∈ Icc 0 1})
          · have hz'strip : z' ∈ {w | 0 ≤ w.re ∧ w.re ≤ 1} := by {
              rw[subset_def] at hrangeclos
              exact hrangeclos z' hz'
            }
            have := ContinuousOn.restrict (DiffContOnCl.continuousOn hf)
            rw[closure_strip] at this
            simp at this
            simp
            apply Tendsto.comp (y:= nhds (f z'))
            · apply Continuous.tendsto continuous_norm
            · rw[tendsto_nhdsWithin_iff_subtype hz'strip]
              apply Continuous.tendsto
              exact this
          · apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
            · exact hφ₂
            · filter_upwards
              intro n
              specialize hz (φ n)
              simp
              exact hz.1
        }

        have hsup : Complex.abs (f z') = sSup ((fun z ↦ Complex.abs (f z)) '' {z | z.re ∈ Icc 0 1}) := tendsto_nhds_unique hu' hu2

        have hmax : IsMaxOn (norm ∘ f) { w:ℂ  | w.re ∈ Icc 0 1} z' := by{
          simp[IsMaxOn, IsMaxFilter]
          intro w hw₁ hw₂
          rw[hsup]
          apply le_csSup_of_le (abs_fun_bounded h2f) (b:= Complex.abs (f w)) ?_ (by simp)
          simp
          use w
        }


        have hmax' : IsMaxOn (norm ∘ f) { w:ℂ  | w.re ∈ Ioo 0 1} z' := by{
          apply IsMaxOn.on_subset hmax
          simp; intro z hz₁ hz₂
          constructor
          · exact le_of_lt hz₁
          · exact le_of_lt hz₂
        }


        by_cases h : z' ∈ { w : ℂ | w.re ∈ Ioo 0 1}
        · have := Complex.norm_eqOn_closure_of_isPreconnected_of_isMaxOn (isPreconnected_strip) (isOpen_strip) hf h hmax'
          simp[EqOn] at this
          have h0 : Complex.abs (f 0) = Complex.abs (f z') := by{
            apply this
            have hcl := closure_strip
            simp at hcl
            rw[hcl]
            simp
          }
          have hpt : Complex.abs (f (t + I*y)) = Complex.abs (f z') := by {
            apply this
            have hcl := closure_strip
            simp at hcl
            rw[hcl]
            simp
            constructor
            · exact ht
            · exact Real.le_one_of_add_nonneg_eq_one hs hts
          }
          simp
          rw[hpt, ← h0]
          specialize h₀f 0
          simp at h₀f
          exact h₀f

        · have : z'.re = 0 ∨ z'.re = 1 := by{
            simp at h
            have : z'.re ≥ 0 ∧ z'.re ≤ 1 := by{
              specialize hrangeclos hz'
              simp at hrangeclos
              tauto
            }
            by_cases hc: z'.re = 0
            · left; assumption
            · right
              specialize h (lt_of_le_of_ne this.1 (Ne.symm hc) )
              exact eq_of_le_of_le this.2 h
          }
          simp[IsMaxOn, IsMaxFilter] at hmax
          specialize hmax (t+I*y)
          simp at hmax
          specialize hmax ht (Real.le_one_of_add_nonneg_eq_one hs hts)
          obtain hz'₁|hz'₂ := this
          · specialize h₀f (z'.im)
            have : z' = I * z'.im := by {
              nth_rewrite 1 [← Complex.re_add_im z']
              simp[hz'₁, mul_comm]
            }
            rw[this] at hmax
            calc
            _ ≤ _ := hmax
            _ ≤ _ := h₀f
          · specialize h₁f (z'.im)
            have : z' = 1 + I * z'.im := by {
              nth_rewrite 1 [← Complex.re_add_im z']
              simp[hz'₂, mul_comm]
            }
            rw[this] at hmax
            calc
            _ ≤ _ := hmax
            _ ≤ _ := h₁f
      · simp at h
        specialize h (t + I * y)
        simp at h
        specialize h ht (Real.le_one_of_add_nonneg_eq_one hs hts)
        rw[h]
        simp
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
  rw[isBounded_iff_forall_norm_le]
  obtain ⟨R, hR⟩:= (isBounded_iff_forall_norm_le).mp h2f
  use R
  intro x hx
  simp at hx
  obtain ⟨z, hz₁, hz₂⟩ := hx
  rw[← hz₂]
  specialize hR (f z) (by use z; simp; exact hz₁)
  simp
  calc
  _ ≤ _ := perturb_bound f ε z
  _ ≤ R := by {
    rw[← mul_one R]
    gcongr
    · calc
      _ ≤ _ := AbsoluteValue.nonneg Complex.abs (f z)
      _ ≤ R := hR
    · exact hR
    · exact bound_factor_le_one hε hz₁
  }
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

lemma perturb_vanish_infty {f:ℂ → ℂ} (h2f : IsBounded (f '' { z | z.re ∈ Icc 0 1})) {ε : ℝ} (hε: ε > 0) : Tendsto (perturb f ε) (Bornology.cobounded ℂ ⊓ Filter.principal ({ z: ℂ | z.re ∈ Icc 0 1})) (nhds 0) := by{
  simp[Tendsto]
  intro A hA
  rw[mem_map, Filter.mem_inf_iff]
  simp
  use { z | z.re ∈ Icc 0 1}ᶜ ∪ (perturb f ε)⁻¹' A
  constructor
  · rw[← Bornology.isCobounded_def, ← Bornology.isBounded_compl_iff]
    simp
    rw[isBounded_iff_forall_norm_le]
    simp
    obtain ⟨r, hr₁, hr₂⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_closedBall_subset hA)
    specialize hr₂ (r/2) (by simp; rw[abs_of_pos hr₁]; simp; exact hr₁)

    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp h2f
    have hM' : 0 < M ∨  0 = M := by{ --this could indeed be zero if the function f is constantly zero
      rw[← le_iff_lt_or_eq]
      specialize hM (f 0) (by use 0; simp)
      calc
      0 ≤ Complex.abs (f 0) := AbsoluteValue.nonneg Complex.abs (f 0)
      _ ≤ M := hM
    }
    obtain hM'₁| hM'₂ := hM'
    · use Real.sqrt (1 + (Real.log M - Real.log (r/2) )/ε)
      intro z hz₁ hz₂ hz₃
      have hball := Set.not_mem_subset hr₂ hz₃
      simp at hball
      rw[Complex.abs_eq_sqrt_sq_add_sq]
      apply Real.sqrt_le_sqrt
      gcongr
      · rw[sq_le_one_iff hz₁]; exact hz₂
      · rw[← mul_le_mul_left hε, ← mul_comm_div, div_self (ne_of_gt hε)]
        simp
        have : r/2 < M * Real.exp (ε * ((z.re)^2 - 1 - (z.im)^2)) := by{
          calc
          _ < _ := hball
          _ ≤ _ := perturb_bound f ε z
          _ ≤ _ := by {gcongr; specialize hM (f z) (by use z; simp[hz₁, hz₂]); exact hM}
        }

        have hr₁' : r/2 > 0 := by simp[hr₁]
        have hrhs : 0 < M * Real.exp (ε * (z.re ^ 2 - 1 - z.im ^ 2)) := by{
          apply Real.mul_pos hM'₁
          apply Real.exp_pos
        }
        rw[← Real.log_lt_log_iff hr₁' hrhs, Real.log_mul (ne_of_gt hM'₁) (by apply Real.exp_ne_zero), Real.log_exp] at this
        apply le_of_lt
        rw[← add_lt_add_iff_right (Real.log (r/2))]
        simp
        have haux : ε * (z.re ^ 2 - 1 - z.im ^ 2) = ε * (z.re^2 - 1) - ε * z.im^2 := by ring
        rw[haux, ← add_sub_assoc, ← add_lt_add_iff_right (ε * z.im ^ 2)] at this
        simp at this
        rw[add_comm]
        have hre : ε * (z.re ^ 2 - 1) ≤ 0 := by{
          rw[mul_nonpos_iff]
          left
          constructor
          · exact le_of_lt hε
          · simp; rw[_root_.abs_of_nonneg hz₁]; exact hz₂
        }

        calc
        _ < _ := this
        _ ≤ Real.log M := by simp[hre]

    · use 0 --Any number works here
      intro z hz₁ hz₂ hz₃
      -- hz₃ cannot happen, so we get a contradiction
      have hA' := mem_of_mem_nhds hA
      have : perturb f ε z = 0 := by{
        simp[perturb]; left
        rw[← AbsoluteValue.eq_zero Complex.abs]
        apply eq_of_le_of_le
        · specialize hM (f z) (by use z; simp[hz₁, hz₂])
          rw[← hM'₂] at hM
          exact hM
        · exact AbsoluteValue.nonneg Complex.abs (f z)
      }
      rw[this] at hz₃
      contradiction
  · use { z | z.re ∈ Icc 0 1} ∪  (perturb f ε)⁻¹' A
    constructor
    · simp
    · ext z
      constructor
      · intro h
        simp[h]
      · intro h
        simp at h
        obtain ⟨h1, h2⟩ := h
        obtain hc1|hc2 := h1
        · obtain hd1|hd2 := h2
          · specialize hc1 hd1.1
            have : (1: ℝ) < (1:ℝ ) := by {
              calc
              1 < z.re := by simp[hc1]
              _ ≤ 1 := by simp[hd1.2]
            }
            norm_num at this
          · simp[hd2]
        · simp[hc2]
}


lemma perturb_bound_strip {f : ℂ → ℂ} {ε : ℝ} (hε: ε > 0)
    (hf : DiffContOnCl ℂ f { z | z.re ∈ Ioo 0 1})
    (h2f : IsBounded (f '' { z | z.re ∈ Icc 0 1}))
    (h₀f : ∀ y : ℝ, ‖f (I * y)‖ ≤ 1) (h₁f : ∀ y : ℝ, ‖f (1 + I * y)‖ ≤ 1)
    {y t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) : ‖perturb f ε (t + I*y)‖ ≤ 1 := by {
      apply DiffContOnCl.norm_le_pow_mul_pow''' ?_ ?_ ?_ ?_ ht hs hts ?_
      · exact perturb_diffcontoncl hf ε
      · exact perturb_isbounded h2f hε
      · exact perturb_bound_left h₀f hε
      · exact perturb_bound_right h₁f hε
      · exact perturb_vanish_infty h2f hε
    }


lemma perturb_pointwise_converge {f : ℂ → ℂ} (z: ℂ) : Tendsto (fun ε ↦ perturb f ε z) (nhds 0) (nhds (f z)) := by{
  simp[perturb]
  have : (fun ε ↦ f z * bump ε z) = fun ε ↦ (((fun _ ↦ f z) ε)  * ((fun t ↦ bump t z) ε)) := rfl
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

lemma DiffContOnCl.const_cpow {a: ℂ} (ha: a ≠ 0) {s: Set ℂ} {f: ℂ → ℂ} (hf: DiffContOnCl ℂ f s) : DiffContOnCl ℂ (fun (z:ℂ) ↦ a^ (f z)) s := by{
  apply DiffContOnCl.mk
  · apply DifferentiableOn.const_cpow
    · exact hf.differentiableOn
    · left; exact ha
  · apply ContinuousOn.const_cpow
    · exact hf.continuousOn
    · left; exact ha
}

lemma DiffContOnCl.id [NormedSpace ℂ E] {s: Set E} : DiffContOnCl ℂ (fun x : E ↦ x) s := DiffContOnCl.mk differentiableOn_id continuousOn_id

-- needed for fun_prop
lemma DiffContOnCl.neg' [NormedSpace ℂ E] [NormedSpace ℂ E₂] {f : E → E₂} {s: Set E}
  (h : DiffContOnCl ℂ f s) : DiffContOnCl ℂ (fun x : E ↦ -(f x)) s := h.neg

attribute [fun_prop] DiffContOnCl
attribute [fun_prop] DiffContOnCl.smul DiffContOnCl.add diffContOnCl_const DiffContOnCl.sub
  DiffContOnCl.neg' DiffContOnCl.sub_const DiffContOnCl.const_cpow DiffContOnCl.id

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
        fun_prop (discharger := norm_cast; positivity)
      }
      have h2g:  IsBounded (g '' { z | z.re ∈ Icc 0 1}) := by {
        obtain ⟨R, hR⟩ :=  isBounded_iff_forall_norm_le.mp h2f
        rw[isBounded_iff_forall_norm_le]
        let A := max 1 (1/M₀)
        let B := max 1 (1/M₁)
        use A*B*R
        intro w hw
        simp at hw
        obtain ⟨z, hz₁, hz₂, hz₃⟩ := hw
        simp[g]
        gcongr
        · apply pow_bound₀ hM₀ (by simp; exact hz₁)
        · apply pow_bound₁ hM₁ (by simp; exact hz₁)
        · exact hR (f z) (by use z; simp[hz₁])
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
        simp
        rw[← inv_mul_cancel (ne_of_gt hM₀)]
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
        rw[← inv_mul_cancel (ne_of_gt hM₁)]
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
      simp[eq_sub_of_add_eq (add_comm t s ▸ hts)]
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

      have hb_sub_a: b - a ≠ 0 := by {
        apply ne_of_gt
        simp[hab]
      }

      have hts'' : s = 1-t := eq_sub_of_add_eq (add_comm t s ▸ hts)

      have hax: x ≥ a := by{
        simp[hx]
        rw[eq_sub_of_add_eq hts]
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

      let g : ℂ → ℂ := fun z ↦ f (a + z * (b-a))
      have hg: DiffContOnCl ℂ g { z | z.re ∈ Ioo 0 1} := by{
        let h : ℂ → ℂ := fun z ↦ a + z *(b-a)
        have hcomp: g = f ∘ h := rfl
        rw[hcomp]
        apply DiffContOnCl.comp (s:={ z | z.re ∈ Ioo a b})
        · exact hf
        · simp[h]
          apply DiffContOnCl.const_add
          have : (fun (x:ℂ) ↦ x * (↑b - ↑a) ) = (fun (x:ℂ) ↦ x • ((b:ℂ) - (a:ℂ))) := rfl
          rw[this]
          apply DiffContOnCl.smul_const
          exact DiffContOnCl.id
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
        use ↑a + w * (↑b - ↑a)
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
        intro y
        specialize h₀f (y* (b-a))
        simp at h₀f
        rw[mul_assoc]
        exact h₀f
      }

      have h₁g : ∀ y : ℝ, ‖g (1 + I * y)‖ ≤ M₁ := by{
        simp only [g]
        simp
        intro y
        specialize h₁f (y * (b-a))
        simp at h₁f
        have : ↑a + (1 + I * ↑y) * (↑b - ↑a) = ↑b + I * (↑y * (↑b - ↑a)) := by ring
        rw[this]
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

      have hgoal := DiffContOnCl.norm_le_pow_mul_pow₀₁ hg h2g hM₀ hM₁ h₀g h₁g ht' hs' hts' (y:=y/(b-a))

      simp [g] at hgoal
      simp only[t'] at hgoal
      simp at hgoal
      rw[add_mul, mul_comm_div, div_self (by norm_cast), mul_assoc, mul_comm_div, div_self (by norm_cast), ← add_assoc] at hgoal
      simp at hgoal

      have ht'₁: t'=((t - 1) * a + s * b)/(b-a) := by{
        simp only [t', hx]
        ring
      }
      simp only [s'] at hgoal
      rw[← ht'₁]
      assumption
    }

-- the following work proves that Lp norm of a function can be approximated by simple functions with Lq norm ≤ 1
variable (E p μ) in
def Lp.simpleLe1 := {g : SimpleFunc α E // snorm g p μ ≤ 1}

def SimpleFunc.toLpSimpLe1 (q : ℝ≥0) (hq : q ≠ 0) (f : SimpleFunc α ℝ≥0) (h : (∫⁻ a, (f a) ^ (q : ℝ) ∂ μ) ^ (q : ℝ)⁻¹ ≤ 1) : Lp.simpleLe1 ℂ q μ where
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
  property := by simp [snorm, snorm', hq]; exact h

section

open SimpleFunc

namespace MeasureTheory

lemma mul_lintegral_eq_iSup_mul_eapprox_lintegral {f g: α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ a, (f * g) a ∂μ = ⨆ n, ∫⁻ a, (f * (eapprox g n)) a ∂μ := by
    calc  ∫⁻ a, (f * g) a ∂μ = ∫⁻ a, ⨆ n, (f * (eapprox g n)) a ∂μ := by {
       congr
       ext a
       simp only [Pi.mul_apply, ← ENNReal.mul_iSup, iSup_eapprox_apply g hg]
       }
    _ = ⨆ n, ∫⁻ a, (f * (eapprox g n)) a ∂μ := by
      apply lintegral_iSup
      . measurability
      . intro i j h a
        simp only [Pi.mul_apply]
        gcongr
        exact monotone_eapprox g h a

lemma snorm_eq_lintegral_rpow_nnnorm' (f : α → E) (p : ℝ≥0) (hp : p ≠ 0): (snorm f p μ) ^ (p : ℝ) = (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) := by
  rw [snorm_eq_lintegral_rpow_nnnorm (by norm_num; exact hp) (by norm_num), ← ENNReal.rpow_mul, coe_toReal, one_div, inv_mul_cancel (by norm_num; exact hp), ENNReal.rpow_one]

lemma ae_lt_top_of_LpNorm_ne_top {f : α → ℝ≥0∞} {p : ℝ≥0} (hp : p ≠ 0) (hf : Measurable f) (h' : (∫⁻ (a : α), f a ^ (p : ℝ) ∂μ) ^ (p : ℝ)⁻¹ ≠ ⊤) : ∀ᵐ (a : α) ∂μ, f a < ⊤ := by
  have : {a | f a < ⊤} = {a | (f a) ^ (p : ℝ) < ⊤} := by
    ext _
    apply (ENNReal.rpow_lt_top_iff_of_pos (by norm_num; exact hp.bot_lt)).symm
  rw [Filter.Eventually, this]
  apply ae_lt_top (hf.pow_const _)
  rw [← lt_top_iff_ne_top] at h'
  rwa [← lt_top_iff_ne_top, ← ENNReal.rpow_lt_top_iff_of_pos (y := (p : ℝ)⁻¹) (by norm_num; exact hp.bot_lt)]

lemma snorm_eq_sSup_snorm (p q : ℝ≥0) (hpq : NNReal.IsConjExponent p q) (f : α → ℂ) (hf : Measurable f) (hf' : snorm f p μ ≠ ∞) (hf0 : snorm f p μ ≠ 0):
snorm f p μ = sSup {snorm (f * (g.1 : α → ℂ)) 1 μ | g : Lp.simpleLe1 ℂ q μ} := by
  apply le_antisymm ?_
  . apply sSup_le
    rintro b ⟨g, hg⟩
    rw [← hg]
    calc snorm (f * (g.1 : α → ℂ)) 1 μ = ∫⁻ a, ‖f a‖₊ * ‖g.1 a‖₊ ∂μ := by simp [snorm, snorm']
    _ = ∫⁻ a, ((‖f ·‖₊) * (‖(g.1 : α → ℂ) ·‖₊)) a ∂μ := lintegral_congr (by simp only [Pi.mul_apply, ENNReal.coe_mul, implies_true])
    _ ≤ snorm f p μ * snorm g.1 q μ  := by
      simp only [snorm, coe_toReal, snorm', ENNReal.coe_eq_zero,
      hpq.ne_zero, ↓reduceIte, coe_ne_top, hpq.symm.ne_zero]
      apply ENNReal.lintegral_mul_le_Lp_mul_Lq _ (NNReal.IsConjExponent.coe hpq) hf.ennnorm.aemeasurable (AEMeasurable.ennnorm (SimpleFunc.aemeasurable _))
    _ ≤ snorm f p μ := mul_le_of_le_one_right (by positivity) g.2
  . rcases eq_or_ne (snorm f p μ) 0 with hf0 | hf0
    . simp [hf0]
    . set g : α → ℝ≥0∞ := ENNReal.ofNNReal ∘ fun a ↦ ‖f a‖₊ ^ ((p : ℝ) - 1) * (snorm f p μ).toNNReal ^ (1 - (p : ℝ))
      have g_meas : Measurable g :=
        ((hf.nnnorm.pow_const _).mul_const _).coe_nnreal_ennreal
      have g_norm : (∫⁻ (a : α), g a ^ (q : ℝ) ∂μ) ^ (q : ℝ)⁻¹ = 1 := by
        simp only [g, Function.comp_apply, ENNReal.coe_mul]
        calc (∫⁻ (a : α), ↑(‖f a‖₊ ^ ((p : ℝ) - 1) * (snorm f p μ).toNNReal ^ (1 - (p : ℝ))) ^ (q : ℝ) ∂μ) ^ (q : ℝ)⁻¹ = (∫⁻ (a : α), (↑‖f a‖₊ ^ (((p : ℝ) - 1) * q) * (snorm f p μ).toNNReal ^ ((1 - (p : ℝ)) * q)) ∂μ) ^ (q : ℝ)⁻¹ := by congr 1; apply lintegral_congr (by intro a; simp; rw [ENNReal.mul_rpow_of_nonneg (hz := by norm_num),
        ← ENNReal.coe_rpow_of_nonneg _ (by norm_num; exact hpq.one_le),
        ← ENNReal.coe_rpow_of_ne_zero (by rw [ENNReal.toNNReal_ne_zero]; exact ⟨hf0, hf'⟩),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul])
        _ = 1 := by
          rw [lintegral_mul_const _ ((Measurable.pow_const hf.ennnorm) _),
          (isConjExponent_coe.mpr hpq).sub_one_mul_conj, ENNReal.coe_toNNReal hf',
          ← snorm_eq_lintegral_rpow_nnnorm' _ _ hpq.ne_zero, ← ENNReal.rpow_add _ _ hf0 hf',
          sub_mul (1 : ℝ), (isConjExponent_coe.mpr hpq).mul_eq_add, one_mul,
          sub_add_cancel_right, add_right_neg, ENNReal.rpow_zero, ENNReal.one_rpow]
      have f_norm : ∫⁻ (a : α), ‖f a‖₊ * (g a) ∂ μ = snorm f p μ := by
        simp only [g, Function.comp_apply]
        calc ∫⁻ (a : α), ↑‖f a‖₊ * (↑(‖f a‖₊ ^ ((p : ℝ) - 1)) * ↑((snorm f p μ).toNNReal ^ (1 - (p : ℝ)))) ∂μ = ∫⁻ (a : α), ↑‖f a‖₊ ^ (p : ℝ) * ↑((snorm f p μ).toNNReal ^ (1 - (p : ℝ))) ∂μ := lintegral_congr (by
              intro _; rw [← mul_assoc]; congr
              rw [← ENNReal.rpow_one ↑‖f _‖₊,← ENNReal.coe_rpow_of_nonneg _ (by norm_num; exact hpq.one_le), ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num; exact hpq.one_le), ENNReal.rpow_one, add_sub_cancel]
              )
        _ = (∫⁻ (a : α), ↑‖f a‖₊ ^ (p : ℝ) ∂ μ) * ↑((snorm f p μ).toNNReal ^ (1 - (p : ℝ))) := by
          rw [lintegral_mul_const _ ((Measurable.pow_const hf.ennnorm) _)]
        _ = snorm f p μ := by
          rw [← snorm_eq_lintegral_rpow_nnnorm' _ _ hpq.ne_zero, ← ENNReal.coe_rpow_of_ne_zero (ENNReal.toNNReal_ne_zero.mpr ⟨hf0, hf'⟩), ENNReal.coe_toNNReal hf', ← ENNReal.rpow_add _ _ hf0 hf', add_sub_cancel, ENNReal.rpow_one]
      calc snorm f p μ = ∫⁻ (a : α), ‖f a‖₊ * (g a) ∂ μ := f_norm.symm
      _ = ⨆ n, ∫⁻ a, ↑‖f a‖₊  * (eapprox g n a) ∂μ := by
        apply mul_lintegral_eq_iSup_mul_eapprox_lintegral (f := fun a ↦ (‖f a‖₊ : ℝ≥0∞)) hf.ennnorm g_meas
      _ ≤ sSup {∫⁻ (a : α), ‖f a‖₊ * (g.1 a) ∂ μ | g : {f : SimpleFunc α ℝ≥0∞ // (∫⁻ a, (f a) ^ (q : ℝ) ∂ μ) ^ (q : ℝ)⁻¹ ≤ 1} } := by
        apply iSup_le; intro n; apply le_sSup
        simp only [Subtype.exists, exists_prop, mem_setOf_eq]
        use eapprox g n
        exact ⟨by
          apply le_trans ?_ g_norm.le
          gcongr
          rw [← iSup_eapprox_apply _ g_meas]
          apply le_iSup _ n, rfl⟩
      _ ≤ sSup {∫⁻ (a : α), ‖f a‖₊ * (g.1 a) ∂ μ | g : {f : SimpleFunc α ℝ≥0 // (∫⁻ a, (f a) ^ (q : ℝ) ∂ μ) ^ (q : ℝ)⁻¹ ≤ 1} } := by
        gcongr
        rintro x ⟨h, hh⟩
        have ae := ae_lt_top_of_LpNorm_ne_top hpq.symm.ne_zero (SimpleFunc.measurable _) (ne_top_of_le_ne_top one_ne_top h.2)
        have : (∫⁻ (a : α), ↑(h.1 a).toNNReal ^ (q : ℝ) ∂μ) ^ (q : ℝ)⁻¹ = (∫⁻ (a : α), (h.1 a) ^ (q : ℝ) ∂μ) ^ (q : ℝ)⁻¹ := by
          congr 1
          apply lintegral_congr_ae
          rw [Filter.EventuallyEq, Filter.Eventually, ← Filter.exists_mem_subset_iff]
          use {a | h.1 a < ⊤}
          exact ⟨ae, by simp; intro a ha; rw [ENNReal.coe_toNNReal ha.ne_top]⟩
        use ⟨SimpleFunc.map ENNReal.toNNReal h.1, by simp [this, h.2]⟩
        simp [← hh]
        apply lintegral_congr_ae
        rw [Filter.EventuallyEq, Filter.Eventually, ← Filter.exists_mem_subset_iff]
        use {a | h.1 a < ⊤}
        exact ⟨ae, by simp; intro a ha; rw [ENNReal.coe_toNNReal ha.ne_top]⟩
      _ ≤ sSup {snorm (f * (g.1 : α → ℂ)) 1 μ | g : Lp.simpleLe1 ℂ q μ} := by
        gcongr; rintro x ⟨h, hh⟩
        use toLpSimpLe1 q hpq.symm.ne_zero _ h.2
        convert hh
        simp [snorm, snorm', toLpSimpLe1]

end MeasureTheory
end

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

lemma lintegral_mul_le_segment_exponent_aux {p₀ p₁ p : ℝ≥0∞} {t s : ℝ≥0} (hp₀ : 0 < p₀)
(hp₁ : 0 < p₁) (hp₀₁ : p₀ < p₁) (hp : p⁻¹ = s / p₀ + t / p₁)
(f : α → E) (hf : AEMeasurable f μ) (hp0' : p ≠ 0) (ht0' : t ≠ 0) (hs0' : s ≠ 0) :
∫⁻ (a : α), ↑‖f a‖₊ ^ (↑s * p.toReal) * ↑‖f a‖₊ ^ (↑t * p.toReal) ∂μ ≤
  snorm (↑f) p₀ μ ^ (↑s * p.toReal) * snorm (↑f) p₁ μ ^ (↑t * p.toReal) := by
  rw [eq_comm] at hp
  rcases eq_or_ne p ⊤ with hpt | hpt'
  simp [hpt, add_eq_zero, hs0', ht0'] at hp
  exact False.elim <| ne_top_of_lt hp₀₁ hp.1

  rcases eq_or_ne p₁ ⊤ with hp₁t | hp₁t'
  simp only [snorm, (ne_of_lt hp₀).symm, ↓reduceIte, LT.lt.ne_top hp₀₁, snorm',
  one_div, hp₁t, top_ne_zero, snormEssSup]
  simp only [hp₁t, div_top, add_zero] at hp
  apply_fun (fun x ↦ x * p₀) at hp
  rw [ENNReal.div_mul_cancel hp₀.ne.symm (ne_top_of_lt hp₀₁)] at hp
  have hp_aux : s * p = p₀ := by rw [hp, mul_assoc, mul_comm p₀, ← mul_assoc,
  ENNReal.inv_mul_cancel hp0' hpt', one_mul]

  apply le_trans (lintegral_mul_le_one_top _ (AEMeasurable.pow_const hf.ennnorm _)) (le_of_eq _)
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
  apply le_trans (ENNReal.lintegral_mul_le_Lp_mul_Lq μ (by apply InSegment.toIsConjugateExponent p₀ p₁ p t s; repeat assumption) (AEMeasurable.pow_const hf.ennnorm _) (AEMeasurable.pow_const hf.ennnorm _)) (le_of_eq _)

  simp only [← ENNReal.rpow_mul]
  congr

  simp only [toReal_mul, coe_toReal, mul_inv_rev]
  rw [toReal_inv, inv_inv, ← mul_assoc, ← mul_assoc, mul_comm _ p.toReal, mul_assoc p.toReal, mul_comm s.toReal, ← mul_assoc, mul_assoc _ s.toReal,
  mul_inv_cancel (ENNReal.toReal_ne_zero.mpr ⟨hp0', hpt'⟩), mul_inv_cancel (by rwa [NNReal.coe_ne_zero]), one_mul, one_mul]

  rotate_left 1

  simp only [toReal_mul, coe_toReal, mul_inv_rev]
  rw [toReal_inv, inv_inv, ← mul_assoc, ← mul_assoc, mul_comm _ p.toReal, mul_assoc p.toReal, mul_comm t.toReal, ← mul_assoc, mul_assoc _ t.toReal,
  mul_inv_cancel (ENNReal.toReal_ne_zero.mpr ⟨hp0', hpt'⟩), mul_inv_cancel (by rwa [NNReal.coe_ne_zero]), one_mul, one_mul]

  repeat' simp [← mul_assoc, ENNReal.toReal_inv]

lemma lintegral_mul_le_segment_exponent {p₀ p₁ p : ℝ≥0∞} {s t : ℝ≥0} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀₁ : p₀ < p₁) (hp : p⁻¹ = s / p₀ + t / p₁) (hst : s + t = 1)
(f : α → E) (hf : AEMeasurable f μ)
 : snorm f p μ ≤ (snorm f p₀ μ) ^ (s : ℝ) * (snorm f p₁ μ) ^ (t : ℝ) := by
  rw [eq_comm] at hp
  have hp0' : p ≠ 0 := by
    by_contra h
    simp [h, ENNReal.inv_zero, add_eq_top, ENNReal.div_eq_top, hp₀.ne.symm, hp₁.ne.symm] at hp

  rcases eq_or_ne t 0 with ht0 | ht0'
  simp only [ht0, add_zero] at hst
  simp only [hst, ENNReal.coe_one, one_div, ht0, ENNReal.coe_zero, ENNReal.zero_div, add_zero,
    inv_inj] at hp
  simp only [hp, hst, NNReal.coe_one, ENNReal.rpow_one, ht0, NNReal.coe_zero, ENNReal.rpow_zero,
    mul_one, le_refl]

  rcases eq_or_ne s 0 with hs0 | hs0'
  simp only [hs0, zero_add] at hst
  simp only [hs0, ENNReal.coe_zero, ENNReal.zero_div, hst, ENNReal.coe_one, one_div, zero_add,
    inv_inj] at hp
  simp only [hs0, NNReal.coe_zero, ENNReal.rpow_zero, hp, hst, NNReal.coe_one, ENNReal.rpow_one,
    one_mul, le_refl]

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
      rw [eq_comm] at hp
      apply lintegral_mul_le_segment_exponent_aux
      <;> assumption
    _ = (snorm f p₀ μ) ^ s.toReal * (snorm f p₁ μ) ^ t.toReal := by
      rw [ENNReal.mul_rpow_of_nonneg, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      repeat rw [mul_assoc, mul_inv_cancel (ENNReal.toReal_ne_zero.mpr ⟨hp0', hpt'⟩), mul_one]
      norm_num

/-- Riesz-Thorin interpolation theorem -/
theorem exists_lnorm_le_of_subadditive_of_lbounded {p₀ p₁ q₀ q₁ : ℝ≥0∞} {M₀ M₁ : ℝ≥0}
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hν : q₀ = ∞ → q₁ = ∞ → SigmaFinite ν)
    (T : (α → E₁) →ₗ[ℂ] β → E₂)
    (h₀T : HasStrongType T p₀ q₀ μ ν M₀)
    (h₁T : HasStrongType T p₁ q₁ μ ν M₁)
    {θ η : ℝ≥0} (hθη : θ + η = 1)
    {p q : ℝ≥0∞} (hp : p⁻¹ = θ / p₀ + η / p₁) (hq : q⁻¹ = θ / q₀ + η / q₁)
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) :
    HasStrongType T p q μ ν (M₀ ^ (θ : ℝ) * M₁ ^ (η : ℝ)) := by
      rcases eq_or_ne p₀ p₁ with (hp₀₁ | hp₀₁)
      . simp only [hp₀₁, ← ENNReal.add_div, ← ENNReal.coe_add, hθη, ENNReal.coe_one, one_div, inv_inj] at hp
        intro f hf
        have aesm := (h₀T f (by rwa [hp₀₁, ← hp])).1
        constructor
        exact aesm
        calc snorm (T f) q ν ≤ (snorm (T f) q₀ ν) ^ (θ : ℝ) * (snorm (T f) q₁ ν) ^ (η : ℝ) := by {
          rcases lt_or_le q₀ q₁ with hq₀₁ | hq₀₁
          exact lintegral_mul_le_segment_exponent hq₀ hq₁ hq₀₁ hq hθη _ aesm.aemeasurable
          rcases lt_or_eq_of_le hq₀₁ with hq₀₁ | hq₀₁
          rw [mul_comm]
          apply lintegral_mul_le_segment_exponent hq₁ hq₀ hq₀₁ (by rwa [add_comm]) (by rwa [add_comm]) _ aesm.aemeasurable
          simp only [hq₀₁, ← ENNReal.add_div, ← ENNReal.coe_add, hθη, ENNReal.coe_one, one_div, inv_inj] at hq
          rw [hq₀₁, ← hq, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num), ← NNReal.coe_add, hθη, NNReal.coe_one, ENNReal.rpow_one]
        }
        _ ≤ (M₀ * snorm f p μ) ^ (θ : ℝ) * (M₁ * snorm f p μ) ^ (η : ℝ) := by
          gcongr
          rw [hp, ← hp₀₁] at *
          apply (h₀T f hf).2
          rw [hp] at *
          apply (h₁T f hf).2
        _ = ↑(M₀ ^ (θ : ℝ) * M₁ ^ (η : ℝ)) * snorm f p μ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← mul_assoc, mul_assoc ((M₀ : ℝ≥0∞) ^ (θ : ℝ)), mul_comm _ ((M₁ : ℝ≥0∞) ^ (η : ℝ)), ← mul_assoc, mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num), ← NNReal.coe_add, hθη, NNReal.coe_one, ENNReal.rpow_one, coe_mul, ENNReal.coe_rpow_of_ne_zero hM₀.ne.symm, ENNReal.coe_rpow_of_ne_zero hM₁.ne.symm]
      .  sorry
