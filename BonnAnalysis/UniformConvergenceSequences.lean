import Mathlib.Topology.Sequences
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order
import Mathlib.Order.Filter.Basic
import BonnAnalysis.ConvergingSequences
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib


namespace MeasureTheory
open MeasureTheory
universe u v x w
open Order Set Filter
open Filter


lemma CnstSeqTendstoUniformlyOn {α : Type u} {β : Type v}  {ι : Type x} [UniformSpace β]
 (f : α → β) (p : Filter ι) (s : Set α) : TendstoUniformlyOn (fun n => f) f p s := by
  unfold TendstoUniformlyOn
  simp
  intro u hu
  have : True = ∀ x ∈ s , (f x , f x) ∈ u := by rw [eq_true_eq_id] ; simp ; intro x _ ; apply refl_mem_uniformity hu
  rw [← this]
  simp
lemma SubSeqConvergesUniformly' {α : Type u} {β : Type v}  {ι : Type x} [UniformSpace β]
 {f : α → β} {p : Filter ι} {s : Set α} {φ : ι → ι}
  (hφ : map φ p ≤ p) {F : ι → α → β} (hF : TendstoUniformlyOn F f p s)
  : TendstoUniformlyOn (F ∘ φ) f p s := by
  rw [tendstoUniformlyOn_iff_tendsto]
  rw [tendstoUniformlyOn_iff_tendsto] at hF
  let φ' : ι × α  → ι × α  := fun (x , y) => (φ x , y)
  have hφ' : map φ' (p ×ˢ 𝓟 s) ≤ (p ×ˢ 𝓟 s) := by
    rw [le_def]
    intro q hq
    rw [mem_map]
    rw[mem_prod_iff]
    rw [mem_prod_iff] at hq
    obtain ⟨ t₁ , ht₁ , t₂ , ht₂ , ht ⟩ := hq
    use φ ⁻¹' t₁
    constructor
    · exact hφ ht₁
    · use t₂
      constructor
      · exact ht₂
      · trans φ' ⁻¹' (t₁ ×ˢ t₂)
        · apply subset_rfl
        · exact fun ⦃a⦄ x ↦ ht x
  exact subSeqConverges' hφ' hF
 --
  lemma SubSeqConvergesUniformly {α : Type u} {β : Type v}  [UniformSpace β]
  {f : α → β}  {s : Set α}
  {F : ℕ → α → β} (hF : TendstoUniformlyOn F f atTop s)
  (F' : SubSequence F)
  : TendstoUniformlyOn F' f atTop s :=
    SubSeqConvergesUniformly' (subsequencePreservesTop F'.hφ) hF



lemma UniformContPresUniformConvergence {α : Type u} {β : Type v} {γ : Type w}  {ι : Type x} [TopologicalSpace α] [UniformSpace β] [UniformSpace γ]
 {f : α → β} {p : Filter ι} {s : Set α} {F : ι → α → β} (hF : TendstoUniformlyOn F f p s)
 (g : β → γ) (hg : UniformContinuous g) : TendstoUniformlyOn (fun n => g ∘ F n) (g ∘ f) p s := by
  intro u hu
  have  := hg hu
  let v := hF _ this
  exact v






 --rw [tendstoUniformlyOn_iff_tendsto]
