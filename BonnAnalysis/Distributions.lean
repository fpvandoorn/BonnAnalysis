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
open MeasureTheory
universe u v
open Order Set Filter
open Filter
open scoped Classical
open NNReal Topology


open scoped Topology
open TopologicalSpace
noncomputable section


variable {V : Type u} (k : Type v)
  [NontriviallyNormedField k] [NormedAddCommGroup V]  [NormedSpace k V] (Ω : Opens V) --{ΩisOpen : IsOpen Ω}
/--
structure HasCompactSupportIn (φ : V → k)  : Prop where
  hasCmpctSprt :  HasCompactSupport φ
  sprtinΩ  : tsupport φ ⊆ Ω
  -/
--Set.EqOn

@[ext] structure 𝓓  where
  φ : V → k
  φIsSmooth : ContDiff k ⊤ φ --⊤ φ
  φHasCmpctSupport :  HasCompactSupport φ
  sprtinΩ  : tsupport φ ⊆ Ω

instance  :  CoeFun (𝓓 k Ω) (fun _ => V → k) where
  coe σ := σ.φ
instance : Zero (𝓓 k Ω ) where
    zero := ⟨
      0 ,
      by apply contDiff_const ,
      by rw [hasCompactSupport_def, Function.support_zero' , closure_empty] ; exact isCompact_empty  ,
      by sorry ⟩
instance : Add (𝓓 k Ω ) where
   add := fun φ ψ => ⟨
    φ + ψ ,
    ContDiff.add φ.φIsSmooth ψ.φIsSmooth,
    HasCompactSupport.add φ.φHasCmpctSupport ψ.φHasCmpctSupport  , by sorry ⟩
instance : Neg (𝓓 k Ω ) where
  neg := fun φ =>
    ⟨ - φ , ContDiff.neg φ.φIsSmooth , by sorry , by sorry ⟩
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
    ContDiff.smul  contDiff_const  φ.φIsSmooth   ,
    HasCompactSupport.mul_left φ.φHasCmpctSupport   , by sorry ⟩
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
    ∀ l : ℕ , TendstoUniformly
      (fun n => iteratedFDeriv k l (a n).φ)
                (iteratedFDeriv k l x.φ) atTop
  seq_cnst := fun x => by
    let A : Set (V ) := @tsupport _ _ ⟨ 0 ⟩  _ x.φ --- weird
    constructor
    · use A
      constructor
      · exact x.φHasCmpctSupport
      · intro n
        exact subset_rfl
    · intro l
      rw [← tendstoUniformlyOn_univ ]

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
      rw [← tendstoUniformlyOn_univ ]
      exact SubSeqConvergesUniformly ( tendstoUniformlyOn_univ.mpr (conv l)) ⟨ a'.φ , a'.hφ ⟩


def 𝓓' := (𝓓 k Ω ) →L[k] k

instance :  CoeFun (𝓓' k Ω ) (fun _ => (𝓓 k Ω)  → k ) where
  coe σ := σ.toFun
instance : ConvergingSequences (𝓓' k Ω ) where
  seq := fun AT => ∀ φ : 𝓓 k Ω , Tendsto (fun n => (AT.1 n) φ ) atTop (𝓝 (AT.2 φ))
  seq_cnst := fun T φ => by apply tendsto_const_nhds
  seq_sub := fun hAT A' φ => subSeqConverges (hAT φ) ⟨ _ , A'.hφ ⟩
lemma diffAt (φ : 𝓓 k Ω) {x : V} (p : x ∈ Ω) : DifferentiableAt k φ x := by
            have := ContDiff.differentiable φ.φIsSmooth (OrderTop.le_top 1)
            apply Differentiable.differentiableAt this
            -- rw [mem_nhds_iff]
            -- use Ω
            -- exact ⟨ by exact fun ⦃a⦄ a ↦ trivial , Ω.isOpen , p ⟩

notation  A "°" T => T ∘L A
lemma zeroCase {φ : ℕ → (V → k)} {φ0 : V → k} :
  (TendstoUniformly (fun n ↦ iteratedFDeriv k 0 (φ n)) (iteratedFDeriv k 0 φ0) atTop) ↔
    TendstoUniformly (fun n => (φ n) ) (φ0) atTop := by

        rw [iteratedFDeriv_zero_eq_comp]
        have myrw : (fun n ↦ iteratedFDeriv k 0 (φ n)) = fun n ↦ (⇑(continuousMultilinearCurryFin0 k V k).symm ∘ (φ n)) := by
          ext1 n
          rw [iteratedFDeriv_zero_eq_comp]
        rw [myrw]
        constructor
        · apply UniformContinuous.comp_tendstoUniformly (g:=⇑(continuousMultilinearCurryFin0 k V k)) ?_
          apply Isometry.uniformContinuous
          apply LinearIsometryEquiv.isometry
        · apply UniformContinuous.comp_tendstoUniformly (g:=⇑(continuousMultilinearCurryFin0 k V k).symm) ?_
          apply Isometry.uniformContinuous
          apply LinearIsometryEquiv.isometry
lemma seqImpliesConvergence   {φ : ℕ → (𝓓 k Ω )} {φ0 : 𝓓 k Ω} (hφ : φ ⟶ φ0) {x : V} :
   Tendsto (fun n => (φ n).φ x) atTop (𝓝 (φ0 x)):= by
    apply TendstoUniformly.tendsto_at ;
    apply (zeroCase k).mp
    exact hφ.2 0

lemma KcontainsSuppOfLimit {α  : ℕ → 𝓓 k Ω} {φ : 𝓓 k Ω } (hφ : α  ⟶ φ)  :
  (∃ K : Set V, (IsCompact K ∧ (∀ n , tsupport (α  n).φ ⊆ K)) ∧ tsupport φ.φ ⊆ K) :=by
  obtain ⟨ K , hK ⟩ := hφ.1
  use K
  constructor
  · exact hK
  · apply closure_minimal ; swap
    · exact IsCompact.isClosed hK.1
    · apply Set.compl_subset_compl.mp
      intro p hp
      simp

      apply tendsto_nhds_unique (f:= fun n => (α n).φ p) (l:=atTop)
      apply seqImpliesConvergence
      exact hφ
      have : (fun n => (α n).φ p) = (fun n => 0) := by
        ext1 n ;
        have : Function.support (α n).φ ⊆ K := by
          trans tsupport (α n).φ ;
          exact subset_tsupport (α n).φ ;
          exact hK.2 n
        exact Function.nmem_support.mp (Set.compl_subset_compl.mpr this hp)
      rw [this]
      apply tendsto_const_nhds















variable (k : Type v) [NontriviallyNormedField k]
  {X : Type w} [ConvergingSequences X] [AddCommMonoid X] [Module k X]
  {M : Type* } [TopologicalSpace M] [AddCommGroup M] [Module k M]

class IsSeqCtsLinearMap (f : X → M) where
  isAdd : ∀ x y, f (x + y) = f x + f y -- we write this out because X might not be a normed space
  isMul : ∀ (c : k) (x), f (c • x) = c • f x
  isSeqCts : SeqContinuous' f
open IsSeqCtsLinearMap

@[simp] def mk  (T : X → M) (hT : IsSeqCtsLinearMap k T) : X →L[k] M  := by
  -- (hT2 : IsLinearMap k T) (hT : SeqContinuous' T) := by
  use ⟨ ⟨ T ,hT.isAdd ⟩ , hT.isMul ⟩
  apply continuous_of_SeqContinuous  hT.isSeqCts
