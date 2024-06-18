import Mathlib.Topology.Sequences
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order
import Mathlib.Order.Filter.Basic
import BonnAnalysis.ConvergingSequences
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.UniformSpace.UniformConvergence
import BonnAnalysis.UniformConvergenceSequences
import Mathlib
--import Mathlib.Analysis.InnerProductSpace
-- import Mathlib.Order
-- noncomputable section
--open FourierTransform MeasureTheory Real


namespace MeasureTheory
open MaesureTheory
universe u v
open Order Set Filter
open Filter
open scoped Classical
open NNReal Topology


open scoped Topology
noncomputable section
structure Open (V : Type u)[TopologicalSpace V]  : Type u where
  subset : Set V
  isOpen : IsOpen subset
instance (V : Type u)[TopologicalSpace V]  :  Coe (Open V) (Set V) where
  coe U := U.subset


variable {V : Type u} (k : Type v)
  [NontriviallyNormedField k] [NormedAddCommGroup V]  [NormedSpace k V] (Ω : Open V) --{ΩisOpen : IsOpen Ω}



@[ext] structure 𝓓  where
  φ : V → k
  φIsSmooth : ContDiffOn k ⊤ φ Ω --⊤ φ
  φHasCmpctSupport : HasCompactSupport φ

instance  :  CoeFun (𝓓 k Ω) (fun _ => V → k) where
  coe σ := σ.φ
instance : Zero (𝓓 k Ω ) where
    zero := ⟨
      0 ,
      by apply contDiffOn_const ,
      by rw [hasCompactSupport_def, Function.support_zero' , closure_empty] ; exact isCompact_empty ⟩
instance : Add (𝓓 k Ω ) where
   add := fun φ ψ => ⟨
    φ + ψ ,
    ContDiffOn.add φ.φIsSmooth ψ.φIsSmooth,
    HasCompactSupport.add φ.φHasCmpctSupport ψ.φHasCmpctSupport  ⟩
instance : Neg (𝓓 k Ω ) where
  neg := fun φ =>
    ⟨ - φ , ContDiffOn.neg φ.φIsSmooth , by sorry ⟩
instance : AddCommGroup (𝓓 k Ω ) where
  add_assoc := fun φ ψ τ => by ext x ; apply add_assoc
  zero_add := fun φ => by ext x ; apply zero_add
  add_zero := fun φ => by ext x ; apply add_zero
  nsmul := nsmulRec
  add_comm := fun φ ψ => by ext x ; apply add_comm

  zsmul := zsmulRec
  add_left_neg := fun φ  => by ext x;apply add_left_neg
  --'neg', 'zsmul', 'add_left_neg'
@[simp] instance : SMul k (𝓓 k Ω ) where
  smul := fun l φ => ⟨ fun x => l * φ x ,
    ContDiffOn.smul  contDiffOn_const  φ.φIsSmooth   ,
    HasCompactSupport.mul_left φ.φHasCmpctSupport   ⟩
instance : Module k (𝓓 k Ω) where

  one_smul := fun φ => by ext x ; exact one_smul k (φ x)
  mul_smul := fun l l' φ => by ext x ; exact mul_smul l l' (φ x)
  smul_zero := fun a => by ext ; exact smul_zero a
  smul_add := fun a φ φ' => by ext x; exact smul_add a (φ x) (φ' x)
  add_smul := fun a b φ => by ext x; exact add_smul a b (φ x)
  zero_smul := fun φ => by ext x; exact zero_smul k (φ x)
-- theorem tendsto_const_nhds {α : Type u} {β : Type v} [TopologicalSpace α] {a : α} {f : Filter β} :
-- Filter.Tendsto (fun x => a) f (nhds a)
open Uniformity
universe w x
instance : ConvergingSequences (𝓓 k Ω) where
  seq := fun (a , x) =>
    (∃ K : Set V , IsCompact K ∧ ∀ n , tsupport (a n).φ ⊆ K) ∧
    ∀ l : ℕ , TendstoUniformlyOn
      (fun n => iteratedFDeriv k l (a n).φ)
                (iteratedFDeriv k l x.φ) atTop univ
  seq_cnst := fun x => by
    let A : Set (V ) := @tsupport _ _ ⟨ 0 ⟩  _ x.φ --- weird
    constructor
    · use A
      constructor
      · exact x.φHasCmpctSupport
      · intro n
        exact subset_rfl
    · intro l
      apply CnstSeqTendstoUniformlyOn
  seq_sub := fun {a} {x} p a' => by
    obtain ⟨⟨ K , ⟨ hK1 , hK2 ⟩  ⟩ , conv ⟩  := p
    constructor
    · use K
      constructor
      · exact hK1
      · intro n
        apply hK2
    · intro l
      --let da' : SubSequence (fun n => iteratedFDeriv k l (a n)) :=
      exact SubSeqConvergesUniformly (conv l) ⟨ a'.φ , a'.hφ ⟩


def 𝓓' := (𝓓 k Ω ) →L[k] k

instance :  CoeFun (𝓓' k Ω ) (fun _ => (𝓓 k Ω)  → k ) where
  coe σ := σ.toFun
instance : ConvergingSequences (𝓓' k Ω ) where
  seq := fun AT => ∀ φ : 𝓓 k Ω , Tendsto (fun n => (AT.1 n) φ ) atTop (𝓝 (AT.2 φ))
  seq_cnst := fun T φ => by apply tendsto_const_nhds
  seq_sub := fun hAT A' φ => subSeqConverges (hAT φ) ⟨ _ , A'.hφ ⟩
lemma diffAt (φ : 𝓓 k Ω) {x : V} (p : x ∈ Ω.subset) : DifferentiableAt k φ x := by
            have := ContDiffOn.differentiableOn φ.φIsSmooth (OrderTop.le_top 1)
            apply DifferentiableOn.differentiableAt this
            rw [mem_nhds_iff]
            use Ω
            exact ⟨ subset_rfl , Ω.isOpen , p ⟩

notation  A "°" T => T ∘L A
