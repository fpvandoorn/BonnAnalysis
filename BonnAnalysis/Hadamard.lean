import Mathlib.Analysis.Complex.Hadamard

open Set Filter Function Complex Topology HadamardThreeLines

lemma Real.sub_ne_zero_of_lt {a b : ℝ} (hab: a < b) : b - a ≠ 0 := by apply ne_of_gt; simp [hab]

namespace Complex

lemma DiffContOnCl.id {s: Set ℂ} : DiffContOnCl ℂ id s :=
  DiffContOnCl.mk differentiableOn_id continuousOn_id

namespace HadamardThreeLines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/--An auxiliary function to prove the general statement of Hadamard's three lines theorem.-/
def scale (f: ℂ → E) (l u : ℝ) : ℂ → E := fun z ↦ f (l + z • (u-l))

/--The transformation on ℂ that is used for `scale` maps the strip ``re ⁻¹' (l,u)``
  to the strip ``re ⁻¹' (0,1)``-/
lemma scale_mapsto_dom {l u : ℝ} (hul: l<u) {z: ℂ} (hz: z ∈ verticalStrip 0 1) :
    l + z * (u-l)  ∈ verticalStrip l u := by {
  simp only [verticalStrip, mem_preimage, mem_Ioo] at hz
  simp only [verticalStrip, mem_preimage, add_re, ofReal_re, mul_re, sub_re, sub_im, ofReal_im,
    sub_self, mul_zero, sub_zero, mem_Ioo, lt_add_iff_pos_right]
  obtain ⟨hz₁, hz₂⟩ := hz
  simp only [hz₁, mul_pos_iff_of_pos_left, sub_pos, hul, true_and]
  rw [add_comm, ← sub_lt_sub_iff_right l, add_sub_assoc, sub_self, add_zero]
  nth_rewrite 2 [← one_mul (u-l)]
  gcongr
  simp only [sub_pos]
  exact hul
}

/--The transformation on ℂ that is used for `scale` maps the closed strip ``re ⁻¹' [l,u]``
  to the closed strip ``re ⁻¹' [0,1]``-/
lemma scale_mapsto_dom_cl {l u : ℝ} (hul: l<u) {z: ℂ} (hz: z ∈ verticalClosedStrip 0 1) :
    l + z * (u-l)  ∈ verticalClosedStrip l u := by {
  simp only [verticalClosedStrip, mem_preimage, add_re, ofReal_re, mul_re, sub_re, sub_im,
    ofReal_im, sub_self, mul_zero, sub_zero, mem_Icc, le_add_iff_nonneg_right]
  simp only [verticalClosedStrip, mem_preimage, mem_Icc] at hz
  obtain ⟨hz₁, hz₂⟩ := hz
  simp only [sub_pos, hul, mul_nonneg_iff_of_pos_right, hz₁, true_and]
  rw [add_comm, ← sub_le_sub_iff_right l, add_sub_assoc, sub_self, add_zero]
  nth_rewrite 2 [← one_mul (u-l)]
  gcongr
  simp only [sub_nonneg]
  exact le_of_lt hul
}

/--If z is on the closed strip `re ⁻¹' [l,u]`, then `(z-l)/(u-l)` is on the closed strip
  `re ⁻¹' [0,1]`.-/
lemma scale_mem_strip {z : ℂ} {l u : ℝ} (hul: l < u) (hz: z ∈ verticalClosedStrip l u) :
    z/(u - l) - l/(u-l) ∈ verticalClosedStrip 0 1 := by{
  simp only [verticalClosedStrip, Complex.div_re, mem_preimage, sub_re, mem_Icc,
    sub_nonneg, tsub_le_iff_right, ofReal_re, ofReal_im, sub_im, sub_self, mul_zero, zero_div,
    add_zero]
  simp only [verticalClosedStrip] at hz
  norm_cast
  simp_rw [Complex.normSq_ofReal, mul_div_assoc, div_mul_eq_div_div_swap,
    div_self (Real.sub_ne_zero_of_lt hul), ← div_eq_mul_one_div]
  constructor
  · gcongr
    · exact le_of_lt (sub_pos.mpr hul)
    · exact hz.1
  · rw [← sub_le_sub_iff_right (l / (u-l)), add_sub_assoc, sub_self, add_zero, div_sub_div_same,
      div_le_one (by simp [hul]), sub_le_sub_iff_right l]
    exact hz.2
}

/-- The function `scale f l u` is `diffContOnCl`. -/
lemma scale_diffContOnCl {f: ℂ → E} {l u : ℝ} (hul: l < u)
    (hd : DiffContOnCl ℂ f (verticalStrip l u)) : DiffContOnCl ℂ (scale f l u)
    (verticalStrip 0 1) := by
  apply DiffContOnCl.comp (s:= verticalStrip l u) hd (DiffContOnCl.const_add
    (DiffContOnCl.smul_const DiffContOnCl.id _) _) _
  rw [MapsTo]
  exact fun z hz ↦ scale_mapsto_dom hul hz

/-- The norm of the function `scale f l u` is bounded above on the closed strip `re⁻¹' [0, 1]`-/
lemma scale_bddAbove {f: ℂ → E} {l u : ℝ} (hul: l< u)
    (hB : BddAbove ((norm ∘ f) '' (verticalClosedStrip l u))) :
    BddAbove ((norm ∘ (scale f l u)) '' (verticalClosedStrip 0 1)) := by{
  obtain ⟨R, hR⟩ := bddAbove_def.mp hB
  rw [bddAbove_def]
  use R
  intro r hr
  obtain ⟨w, hw₁, hw₂, _⟩ := hr
  simp only [comp_apply, scale, smul_eq_mul]
  have : ‖f (↑l + w * (↑u - ↑l))‖ ∈ norm ∘ f '' verticalClosedStrip l u := by{
    simp only [comp_apply, mem_image]
    use ↑l + w * (↑u - ↑l)
    simp only [and_true]
    exact scale_mapsto_dom_cl hul hw₁
  }
  exact hR ‖f (↑l + w * (↑u - ↑l))‖ this
}

/--A bound to the norm of `f` on the line `z.re=l` induces a bound to the norm of
  `scale f l u z` on the line `z.re=0`. -/
lemma scale_bound_left {f: ℂ → E} {l u a : ℝ} (ha : ∀ z ∈ re ⁻¹' {l}, ‖f z‖ ≤ a) :
    ∀ z ∈ re ⁻¹' {0}, ‖scale f l u z‖ ≤ a := by{
  simp only [mem_preimage, mem_singleton_iff, scale, smul_eq_mul]
  exact fun z hz ↦ ha (↑l + z * (↑u - ↑l)) (by simp [hz])
}

/--A bound to the norm of `f` on the line `z.re=u` induces a bound to the norm of `scale f l u z`
  on the line `z.re=1`. -/
lemma scale_bound_right {f: ℂ → E} {l u b : ℝ} (hb : ∀ z ∈ re ⁻¹' {u}, ‖f z‖ ≤ b) :
    ∀ z ∈ re ⁻¹' {1}, ‖scale f l u z‖ ≤ b := by{
  simp only [scale, mem_preimage, mem_singleton_iff, smul_eq_mul]
  exact fun z hz ↦ hb (↑l + z * (↑u - ↑l)) (by simp [hz])
}

/--A technical lemma needed in the proof-/
lemma fun_arg_eq {l u: ℝ} (hul: l < u) (z: ℂ) :
    (↑l + (z / (↑u - ↑l) - ↑l / (↑u - ↑l)) * (↑u - ↑l)) = z := by{
  rw [sub_mul, div_mul_comm, div_self (by norm_cast; exact Real.sub_ne_zero_of_lt hul ),
    div_mul_comm, div_self (by norm_cast; exact Real.sub_ne_zero_of_lt hul)]
  simp
}

/--Another technical lemma needed in the proof-/
lemma bound_exp_eq {l u: ℝ} (hul : l < u) (z:ℂ) :
    (z / (↑u - ↑l)).re - ((l:ℂ) / (↑u - ↑l)).re = (z.re - l) / (u - l) := by
  norm_cast
  rw [Complex.div_re, Complex.normSq_ofReal, Complex.ofReal_re, Complex.ofReal_im, mul_div_assoc,
    div_mul_eq_div_div_swap, div_self (by exact_mod_cast Real.sub_ne_zero_of_lt hul),
    ← div_eq_mul_one_div, mul_zero, zero_div, add_zero, ← div_sub_div_same]

/--The correct generalization of `interpStrip` to produce bounds in the general case-/
noncomputable def interpStrip' (f: ℂ → E) (l u : ℝ) (z : ℂ) : ℂ :=
  if (sSupNormIm f l) = 0 ∨ (sSupNormIm f u) = 0
    then 0
    else (sSupNormIm f l) ^ (1-((z-l)/(u-l))) * (sSupNormIm f u) ^ ((z-l)/(u-l))


/--The supremum of the norm of `scale f l u` on the line `z.re = 0` is the same as the supremum
  of `f` on the line `z.re=l`.-/
lemma sSupNormIm_scale_left (f: ℂ → E) {l u : ℝ} (hul: l < u) :
    sSupNormIm (scale f l u) 0 = sSupNormIm f l := by
  simp_rw [sSupNormIm, image_comp]
  have : scale f l u '' (re ⁻¹' {0}) = f '' (re ⁻¹' {l}) := by
    ext e
    simp only [scale, smul_eq_mul, mem_image, mem_preimage, mem_singleton_iff]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨z, hz₁, hz₂⟩ := h
      use ↑l + z * (↑u - ↑l)
      simp [hz₁, hz₂]
    · obtain ⟨z, hz₁, hz₂⟩ := h
      use ((z-l)/(u-l))
      constructor
      · norm_cast
        rw [Complex.div_re, Complex.normSq_ofReal, Complex.ofReal_re]
        simp [hz₁]
      · rw [div_mul_comm, div_self (by exact_mod_cast Real.sub_ne_zero_of_lt hul)]
        simp [hz₂]
  rw [this]

/--The supremum of the norm of `scale f l u` on the line `z.re = 1` is the same as
  the supremum of `f` on the line `z.re=u`.-/
lemma sSupNormIm_scale_right (f: ℂ → E) {l u : ℝ} (hul: l < u) :
    sSupNormIm (scale f l u) 1 = sSupNormIm f u := by
  simp_rw [sSupNormIm, image_comp]
  have : scale f l u '' (re ⁻¹' {1}) = f '' (re ⁻¹' {u}) := by
    ext e
    simp only [scale, smul_eq_mul, mem_image, mem_preimage, mem_singleton_iff]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨z, hz₁, hz₂⟩ := h
      use ↑l + z * (↑u - ↑l)
      simp only [add_re, ofReal_re, mul_re, hz₁, sub_re, one_mul, sub_im, ofReal_im, sub_self,
        mul_zero, sub_zero, add_sub_cancel, hz₂, and_self]
    · obtain ⟨z, hz₁, hz₂⟩ := h
      use ((z-l)/(u-l))
      constructor
      · norm_cast
        rw [Complex.div_re, Complex.normSq_ofReal, Complex.ofReal_re]
        simp only [sub_re, hz₁, ofReal_re, sub_im, ofReal_im, sub_zero, ofReal_sub, sub_self,
          mul_zero, zero_div, add_zero]
        rw [div_mul_eq_div_div_swap, mul_div_assoc,
          div_self (by exact_mod_cast Real.sub_ne_zero_of_lt hul),
          mul_one, div_self (by exact_mod_cast Real.sub_ne_zero_of_lt hul)]
      · rw [div_mul_comm, div_self (by exact_mod_cast Real.sub_ne_zero_of_lt hul)]
        simp only [one_mul, add_sub_cancel, hz₂]
  rw [this]

/--A technical lemma relating the bounds given by the three lines lemma on a general strip to
the bounds for its scaled version on the strip ``re ⁻¹' [0,1]` to the bounds on a general strip.-/
lemma interpStrip_scale (f: ℂ → E) {l u : ℝ} (hul: l < u) (z : ℂ)  : interpStrip (scale f l u)
    ((z - ↑l) / (↑u - ↑l)) = interpStrip' f l u z := by
  rw [interpStrip, interpStrip', sSupNormIm_scale_left f hul, sSupNormIm_scale_right f hul]

/--
**Hadamard three-line theorem**: If `f` is a bounded function, continuous on the
closed strip `re ⁻¹' [a,b]` and differentiable on open strip `re ⁻¹' (a,b)`, then for
`M(x) := sup ((norm ∘ f) '' (re ⁻¹' {x}))` we have that for all `z` in the closed strip
`re ⁻¹' [a,b]` the inequality `‖f(z)‖ ≤ M(0) ^ (1 - ((z.re-a)/(b-a))) * M(1) ^ ((z.re-a)/(b-a))`
holds. -/
lemma norm_le_interpStrip_of_mem {l u : ℝ} (hul: l < u) {f : ℂ → E} {z : ℂ}
    (hz : z ∈ verticalClosedStrip l u) (hd : DiffContOnCl ℂ f (verticalStrip l u))
    (hB : BddAbove ((norm ∘ f) '' (verticalClosedStrip l u))) :
    ‖f z‖ ≤ ‖interpStrip' f l u z‖ := by{
  have hgoal := norm_le_interpStrip_of_mem_verticalClosedStrip (scale f l u)
    (scale_mem_strip hul hz) (scale_diffContOnCl hul hd) (scale_bddAbove hul hB)
  rw [scale, smul_eq_mul, norm_eq_abs, fun_arg_eq hul, div_sub_div_same,
    interpStrip_scale f hul z] at hgoal
  exact hgoal
}


/-- **Hadamard three-line theorem** (Variant in simpler terms): Let `f` be a
bounded function, continuous on the closed strip `re ⁻¹' [l,u]` and differentiable on open strip
`re ⁻¹' (l,u)`. If, for all `z.re = l`, `‖f z‖ ≤ a` for some `a ∈ ℝ` and, similarly, for all
`z.re = u`, `‖f z‖ ≤ b` for some `b ∈ ℝ` then for all `z` in the closed strip
`re ⁻¹' [l,u]` the inequality `‖f(z)‖ ≤ a ^ (1 - (z.re-l)/(u-l)) * b ^ ((z.re-l)/(u-l))` holds. -/
lemma norm_le_interp_of_mem' {f : ℂ → E} {z : ℂ} {a b l u : ℝ} (hul: l < u)
    (hz : z ∈ verticalClosedStrip l u) (hd : DiffContOnCl ℂ f (verticalStrip l u))
    (hB : BddAbove ((norm ∘ f) '' (verticalClosedStrip l u)))
    (ha : ∀ z ∈ re ⁻¹' {l}, ‖f z‖ ≤ a) (hb : ∀ z ∈ re ⁻¹' {u}, ‖f z‖ ≤ b) :
    ‖f z‖ ≤ a ^ (1 - (z.re-l)/(u-l)) * b ^ ((z.re-l)/(u-l)) := by{

  have hgoal := norm_le_interp_of_mem_verticalClosedStrip' (scale f l u)
    (scale_mem_strip hul hz) (scale_diffContOnCl hul hd) (scale_bddAbove hul hB)
    (scale_bound_left ha) (scale_bound_right hb)
  rw [scale, smul_eq_mul, sub_re, fun_arg_eq hul, bound_exp_eq hul] at hgoal
  exact hgoal
}

end HadamardThreeLines
end Complex
