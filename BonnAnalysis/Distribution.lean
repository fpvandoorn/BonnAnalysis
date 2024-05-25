-- import Mathlib.Analysis.Fourier.FourierTransformDeriv
-- import Mathlib.Analysis.Fourier.Inversion
-- import Mathlib.Analysis.Fourier.PoissonSummation
-- import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Topology.Defs.Sequences
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order
import Mathlib.Order.Filter.Basic
noncomputable section

--open FourierTransform MeasureTheory Real

namespace MeasureTheory

universe u
open Order Set Filter
open Filter
open scoped Topology
lemma isSeqClosedOfClosed {X : Type u} [TopologicalSpace X] ( A: Set X) (p : IsClosed A) :  IsSeqClosed A := by
  intro a a0 ha ha0
  by_contra ha0A
  have : A ᶜ ∈ 𝓝 a0 := IsClosed.compl_mem_nhds p ha0A
  specialize ha0 this
  simp at ha0
  obtain ⟨ x , hx ⟩ := ha0
  exact hx x (Nat.le_refl x) (ha x)




lemma sequentialSpaceUnivProp {X Y : Type u} [TopologicalSpace X]  [TopologicalSpace Y]
(p : SequentialSpace X) {f : X → Y} (pf : SeqContinuous f) : Continuous f := by
  apply continuous_iff_isClosed.mpr
  intro A hA
  apply IsSeqClosed.isClosed
  intro a a0 ha q
  specialize pf q
  have hA := isSeqClosedOfClosed A hA
  exact hA ha pf




lemma lemmaNbhd {X : Type} [TopologicalSpace X]
  (nbh : ( x: X) → Filter X)
  (rfl : ∀ x , ∀ N ∈ nbh x , x ∈ N)
  (interior : ∀ x : X , ∀ N ∈ nbh x ,  { z ∈ N | N ∈ nbh z} ∈ nbh x)
  (as : ∀ {A} ,  IsOpen A ↔ ∀ x ∈ A , A ∈ nbh x ) : nhds = nbh  := by -- @nhds _ (fromConvSeq seq) = nbh seq := by

  funext x
  rw [le_antisymm_iff]
  constructor
  · rw [le_def]
    intro A hA
    rw [@mem_nhds_iff]
    use {a ∈ A | A  ∈ nbh a}
    constructor
    · simp
    · constructor
      · rw [as]
        intro _ hx
        apply interior
        exact hx.2
      · exact rfl x {a | a ∈ A ∧ A ∈ nbh a} (interior x A hA)
  · rw [@le_nhds_iff]
    intro s hxs hs
    exact as.mp hs x hxs
set_option checkBinderAnnotations false
class ConvergingSequences (X : Type u) where
  seq : (ℕ → X) × X → Prop
variable {X : Type u} [ConvergingSequences X]
notation a "⟶" x => seq (a , x)
--notation (priority := high) P "[" A "]" => obj_over (P:=P.1.hom) A
open ConvergingSequences
-- def IsSeqClosed (s : Set X) : Prop := ∀ ⦃x : ℕ → X⦄ ⦃p : X⦄, (∀ n, x n ∈ s) ∧ seq (x , p) → p ∈ s
@[simp] def nbh (x : X) : Filter X := by


  use {Y | ∀ a , (seq (a , x)) → a ⁻¹' Y ∈ atTop}
  · simp
  · simp ; sorry
  · sorry

lemma tendsToNbh  {x : X} (a : ℕ → X) (ha : seq ( a, x)) : Tendsto a atTop (nbh x) := by sorry


instance  : TopologicalSpace X  where
  IsOpen := fun A : Set X ↦ ∀ x ∈ A,  A ∈ nbh x
  isOpen_univ := by simp ; sorry
  isOpen_inter := by sorry -- simp
  isOpen_sUnion:= by sorry -- simp
lemma isSeq : SequentialSpace X where
  isClosed_of_seq := by
    intro A p
    let U := A ᶜ
    rw [← @isOpen_compl_iff]

    intro x hx a ha
    have : (a  ⁻¹' A)ᶜ ∈ atTop := by
      by_contra ass
      simp at ass
      let a' : ℕ → X := by sorry
      have l : ∀ n , a' n ∈ A := by sorry
      have : Tendsto a' atTop (𝓝 x) := by
        have : @nhds X _ = nbh := by
          apply lemmaNbhd nbh
          sorry

        rw [this]
        apply tendsToNbh
        sorry
        --have sa'x : seq (a' , x) := by sorry
        --exact sa'x
      specialize p l this
      exact hx p
    exact this
    /-- fun n ↦ by

      obtain ⟨x , hx⟩  :=  (ass n).choose_spec ;
  --/









  --let seqClos (A: Set X) : (Set X) := { a | ∃ x : ℕ → X, (∀ n : ℕ, x n ∈ A) ∧ seq (x , a) }

  --local instance Filter : PartialOrder := instPartialOrder

 -- apply Order.Filter.Basic.instPartialOrder

lemma univPropfromConvSeq (Y : Type u) [TopologicalSpace Y] (f :X → Y) (pf : ∀ x a,  seq ( x, a) → Tendsto (f ∘ x) atTop (𝓝 (f a))) : Continuous[ fromConvSeq seq , _] f := by
  --local attribute X [fromConvSeq seq]
  have : ∀ x , @ContinuousAt _ _ (fromConvSeq seq) _ f x := fun x ↦ by  unfold ContinuousAt Tendsto ; intro U hU ; simp ; intro a ;   simp ; --pf

-- lemma continuous_generateFrom_iff {t : TopologicalSpace α} {b : Set (Set β)} :
--     Continuous[t, generateFrom b] f ↔ ∀ s ∈ b, IsOpen (f ⁻¹' s) := by
sorry
/--
instance fromConvSequencesIsFrechetUrysohnSpace {X : Type u} (seq : (ℕ → X) × X → Prop)  :
  @FrechetUrysohnSpace X (SpaceGeneratedFromConvSequences seq)  where --
    closure_subset_seqClosure := by sorry

--/
